import hashlib, importlib.util, json, os, shutil, subprocess, tarfile, tempfile, unittest
from pathlib import Path
from unittest import mock

HERE=Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location("archive",HERE/"build_replay_overlay_archive.py")
MOD=importlib.util.module_from_spec(SPEC); assert SPEC.loader is not None; SPEC.loader.exec_module(MOD)
ZSTD=Path(shutil.which("zstd") or "").resolve()
ZSTD_SHA=MOD.sha256_file(ZSTD) if ZSTD.is_file() else ""

def publication(root):
    pub=root/"publication"; overlay=pub/"overlay"; (overlay/"Mathlib").mkdir(parents=True)
    target=overlay/"Mathlib/Test.olean"; target.write_bytes(b"olean\n")
    entries=[{"bytes":target.stat().st_size,"path":"Mathlib/Test.olean","sha256":MOD.sha256_file(target)}]
    manifest={"entry_count":1,"entries":entries,"identity_sha256":hashlib.sha256(MOD.canonical(entries)).hexdigest(),
      "included_extensions":[".olean"],"schema":MOD.OVERLAY.SCHEMA}
    (pub/"manifest.json").write_bytes(MOD.canonical(manifest)); control=[]
    for index,path in enumerate(MOD.OVERLAY.CONTROL_PATHS):
        control.append({"blob_oid":str(index+1)*40,"bytes":1,"path":path,"sha256":str(index+1)*64})
    package={"build_root":"/pkg/.lake/build/lib/lean","facade":"/repo/proofs/.lake/packages/mathlib",
      "head":"a"*40,"manifest_url":"https://github.com/leanprover-community/mathlib4",
      "name":"mathlib","normalized_remote":"github.com/leanprover-community/mathlib4","rev":"a"*40}
    receipt={"control_files":control,"entry_count":1,"git_path":"/usr/bin/git","git_sha256":"4"*64,
      "manifest_path":"manifest.json","manifest_sha256":MOD.sha256_file(pub/"manifest.json"),
      "overlay_identity_sha256":manifest["identity_sha256"],"packages":[package],"producer_path":"/producer.py",
      "producer_sha256":"5"*64,"project_manifest_path":"/selection.tsv","project_manifest_sha256":"6"*64,
      "project_root":"/project","repo":"/repo","schema":MOD.OVERLAY.RECEIPT_SCHEMA,"source_commit":"b"*40}
    (pub/"receipt.json").write_bytes(MOD.canonical(receipt)); return pub

@unittest.skipUnless(ZSTD_SHA,"zstd is required")
class OverlayArchiveTest(unittest.TestCase):
    def test_repeat_identity_verify_and_create_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory).resolve(); pub=publication(root); one=root/"one.tar.zst"; two=root/"two.tar.zst"
            first=MOD.build(pub,one,ZSTD,ZSTD_SHA); second=MOD.build(pub,two,ZSTD,ZSTD_SHA)
            self.assertEqual(one.read_bytes(),two.read_bytes()); self.assertEqual(first["archive_sha256"],second["archive_sha256"])
            self.assertEqual(first["schema"],MOD.ARCHIVE_SCHEMA)
            self.assertEqual(first["zstd_argv"],
                [str(ZSTD),*MOD.ZSTD_COMPRESS,"{tar}","-o","{archive}"])
            self.assertEqual(MOD.unpack_verify(one,ZSTD,ZSTD_SHA)["entry_count"],1)
            with self.assertRaisesRegex(MOD.ArchiveError,"must be absent"): MOD.build(pub,one,ZSTD,ZSTD_SHA)
            sentinel=root/"race.tar.zst"
            def race(): sentinel.write_bytes(b"other")
            with self.assertRaisesRegex(MOD.ArchiveError,"appeared"): MOD.build(pub,sentinel,ZSTD,ZSTD_SHA,race)
            self.assertEqual(sentinel.read_bytes(),b"other")
            drift=root/"drift.tar.zst"
            def mutate_source(): (pub/"overlay/Mathlib/Test.olean").write_bytes(b"changed")
            with self.assertRaisesRegex(MOD.ArchiveError,"input drift|identity drift"):
                MOD.build(pub,drift,ZSTD,ZSTD_SHA,mutate_source)
            self.assertFalse(drift.exists())
            (pub/"overlay/Mathlib/Test.olean").write_bytes(b"olean\n")
            replaced=root/"replaced.tar.zst"; replacement=two.read_bytes()
            def replace_output(): replaced.unlink(); replaced.write_bytes(replacement)
            with self.assertRaisesRegex(MOD.ArchiveError,"ownership/identity drift"):
                MOD.build(pub,replaced,ZSTD,ZSTD_SHA,after_link=replace_output)
            self.assertEqual(replaced.read_bytes(),replacement)
            final_race=root/"final-race.tar.zst"
            def replace_at_result(): final_race.unlink(); final_race.write_bytes(replacement)
            with self.assertRaisesRegex(MOD.ArchiveError,"ownership/identity drift"):
                MOD.build(pub,final_race,ZSTD,ZSTD_SHA,before_result=replace_at_result)
            self.assertEqual(final_race.read_bytes(),replacement)

    def test_publication_tamper_missing_extra_and_legacy_fail(self):
        mutations=(
          lambda p:(p/"overlay/Mathlib/Test.olean").write_bytes(b"bad"),
          lambda p:(p/"receipt.json").unlink(),
          lambda p:(p/"extra").write_bytes(b"x"),
          lambda p:(p/"overlay-oleans.sha256.tsv").write_bytes(b"legacy"))
        for mutate in mutations:
            with self.subTest(mutate=mutate),tempfile.TemporaryDirectory() as directory:
                root=Path(directory).resolve(); pub=publication(root); mutate(pub)
                with self.assertRaises(MOD.ArchiveError): MOD.build(pub,root/"out.zst",ZSTD,ZSTD_SHA)

    def test_archive_metadata_links_traversal_special_and_readback_fail(self):
        kinds=("traversal","symlink","hardlink","fifo","mode","extra")
        for kind in kinds:
            with self.subTest(kind=kind),tempfile.TemporaryDirectory() as directory:
                root=Path(directory).resolve(); pub=publication(root); tar=root/"bad.tar"; archive=root/"bad.tar.zst"
                with tarfile.open(tar,"w",format=tarfile.GNU_FORMAT) as stream:
                    info=tarfile.TarInfo("../escape" if kind=="traversal" else "manifest.json")
                    info.uid=info.gid=0; info.uname=info.gname=""; info.mtime=0; info.mode=0o600 if kind=="mode" else 0o644
                    if kind=="symlink": info.type=tarfile.SYMTYPE; info.linkname="target"; stream.addfile(info)
                    elif kind=="hardlink": info.type=tarfile.LNKTYPE; info.linkname="target"; stream.addfile(info)
                    elif kind=="fifo": info.type=tarfile.FIFOTYPE; stream.addfile(info)
                    else: info.size=1; stream.addfile(info,__import__("io").BytesIO(b"x"))
                subprocess.run([str(ZSTD),*MOD.ZSTD_COMPRESS,str(tar),"-o",str(archive)],check=True)
                with self.assertRaises(MOD.ArchiveError): MOD.unpack_verify(archive,ZSTD,ZSTD_SHA)
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory).resolve(); pub=publication(root); archive=root/"out.zst"; MOD.build(pub,archive,ZSTD,ZSTD_SHA)
            archive.write_bytes(archive.read_bytes()[:-1]+b"x")
            with self.assertRaises(MOD.ArchiveError): MOD.unpack_verify(archive,ZSTD,ZSTD_SHA)

    def test_source_symlink_hardlink_and_special_fail(self):
        for kind in ("symlink","hardlink","fifo"):
            with self.subTest(kind=kind),tempfile.TemporaryDirectory() as directory:
                root=Path(directory).resolve(); pub=publication(root); target=pub/"overlay/Mathlib/Test.olean"
                if kind=="symlink": target.unlink(); target.symlink_to(pub/"manifest.json")
                elif kind=="hardlink": alias=pub/"overlay/Mathlib/Alias.olean"; os.link(target,alias)
                else: target.unlink(); os.mkfifo(target)
                with self.assertRaises((MOD.ArchiveError,MOD.OVERLAY.OverlayError)): MOD.build(pub,root/"out.zst",ZSTD,ZSTD_SHA)

    def test_nested_receipt_identity_spoofs_fail(self):
        mutations=(
          lambda r:r["control_files"][0].__setitem__("blob_oid","g"*40),
          lambda r:r["control_files"][0].__setitem__("bytes",True),
          lambda r:r["packages"][0].__setitem__("name",""),
          lambda r:r["packages"][0].__setitem__("name","../pkg"),
          lambda r:r["packages"][0].__setitem__("normalized_remote","evil"),
          lambda r:r["packages"].append(dict(r["packages"][0],name="duplicate-remote")),
          lambda r:r.__setitem__("project_root","relative"),
          lambda r:r.__setitem__("project_root","/a/../b"),
          lambda r:r["packages"][0].__setitem__("build_root","/a/../b"))
        for mutate in mutations:
            with self.subTest(mutate=mutate),tempfile.TemporaryDirectory() as directory:
                root=Path(directory).resolve(); pub=publication(root); path=pub/"receipt.json"
                receipt=json.loads(path.read_text()); mutate(receipt); path.write_bytes(MOD.canonical(receipt))
                with self.assertRaisesRegex(MOD.ArchiveError,"receipt exact contract"):
                    MOD.build(pub,root/"out.zst",ZSTD,ZSTD_SHA)

if __name__=="__main__": unittest.main()
