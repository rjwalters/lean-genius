#!/usr/bin/env python3
"""Build and verify a deterministic archive of a complete replay overlay publication."""
from __future__ import annotations

import argparse, hashlib, importlib.util, json, os, re, subprocess, tarfile, tempfile
from pathlib import Path, PurePosixPath

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("replay_overlay", HERE / "build_replay_overlay.py")
OVERLAY = importlib.util.module_from_spec(SPEC); assert SPEC.loader is not None; SPEC.loader.exec_module(OVERLAY)

SHA = re.compile(r"[0-9a-f]{64}")
OID = re.compile(r"[0-9a-f]{40}")
ARCHIVE_SCHEMA = "erdos85-h1-replay-complete-olean-overlay-archive-v1"
RECEIPT_FIELDS = {"control_files","entry_count","git_path","git_sha256","manifest_path",
    "manifest_sha256","overlay_identity_sha256","packages","producer_path","producer_sha256",
    "project_manifest_path","project_manifest_sha256","project_root","repo","schema","source_commit"}
CONTROL_FIELDS = {"blob_oid","bytes","path","sha256"}
PACKAGE_FIELDS = {"build_root","facade","head","manifest_url","name","normalized_remote","rev"}
ZSTD_COMPRESS = ("-q","-19","--threads=1","--no-progress","-f")
ZSTD_DECOMPRESS = ("-d","-q","--no-progress","-f")

class ArchiveError(ValueError): pass

def canonical(value):
    return (json.dumps(value,ensure_ascii=True,allow_nan=False,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")

def sha256_file(path):
    digest=hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda:stream.read(1<<20),b""): digest.update(block)
    return digest.hexdigest()

def safe(path,label,kind="file",absent=False):
    if not path.is_absolute() or path!=path.resolve(strict=False): raise ArchiveError(f"{label} is not canonical absolute")
    current=path if path.exists() else path.parent
    while True:
        if current.is_symlink(): raise ArchiveError(f"{label} has symlink ancestry")
        if current==current.parent: break
        current=current.parent
    if absent:
        if path.exists() or path.is_symlink() or not path.parent.is_dir(): raise ArchiveError(f"{label} must be absent")
    elif kind=="file" and (path.is_symlink() or not path.is_file()): raise ArchiveError(f"{label} is not a regular file")
    elif kind=="dir" and (path.is_symlink() or not path.is_dir()): raise ArchiveError(f"{label} is not a directory")

def require(path,pin,label):
    safe(path,label)
    if SHA.fullmatch(str(pin)) is None or sha256_file(path)!=pin: raise ArchiveError(f"{label} hash mismatch")

def read_canonical(path,label):
    safe(path,label); raw=path.read_bytes()
    try: value=json.loads(raw)
    except (UnicodeDecodeError,json.JSONDecodeError) as error: raise ArchiveError(f"{label} malformed JSON") from error
    if not isinstance(value,dict) or raw!=canonical(value): raise ArchiveError(f"{label} serialization mismatch")
    return value,raw

def validate_publication(publication):
    safe(publication,"overlay publication",kind="dir")
    if sorted(x.name for x in publication.iterdir())!=["manifest.json","overlay","receipt.json"]:
        raise ArchiveError("overlay publication exact top-level mismatch")
    manifest,manifest_raw=read_canonical(publication/"manifest.json","overlay manifest")
    receipt,_=read_canonical(publication/"receipt.json","overlay receipt")
    try: count=OVERLAY.verify_tree(publication/"overlay",manifest)
    except (OSError,ValueError) as error: raise ArchiveError(f"overlay tree verification failed: {error}") from error
    controls=receipt.get("control_files"); packages=receipt.get("packages")
    scalar_paths=("git_path","producer_path","project_manifest_path","project_root","repo")
    if (set(receipt)!=RECEIPT_FIELDS or receipt.get("schema")!=OVERLAY.RECEIPT_SCHEMA
            or receipt.get("manifest_path")!="manifest.json" or receipt.get("entry_count")!=count
            or receipt.get("manifest_sha256")!=hashlib.sha256(manifest_raw).hexdigest()
            or receipt.get("overlay_identity_sha256")!=manifest.get("identity_sha256")
            or SHA.fullmatch(str(receipt.get("git_sha256"))) is None
            or SHA.fullmatch(str(receipt.get("producer_sha256"))) is None
            or SHA.fullmatch(str(receipt.get("project_manifest_sha256"))) is None
            or OVERLAY.COMMIT.fullmatch(str(receipt.get("source_commit"))) is None
            or not isinstance(controls,list) or len(controls)!=len(OVERLAY.CONTROL_PATHS)
            or any(not isinstance(x,dict) or set(x)!=CONTROL_FIELDS
                   or SHA.fullmatch(str(x.get("sha256"))) is None
                   or OID.fullmatch(str(x.get("blob_oid"))) is None
                   or not isinstance(x.get("bytes"),int) or isinstance(x.get("bytes"),bool)
                   or x.get("bytes")<=0 for x in controls)
            or [x.get("path") for x in controls]!=list(OVERLAY.CONTROL_PATHS)
            or not isinstance(packages,list) or not packages
            or any(not isinstance(x,dict) or set(x)!=PACKAGE_FIELDS
                   or OVERLAY.COMMIT.fullmatch(str(x.get("head"))) is None
                   or x.get("head")!=x.get("rev")
                   or any(not isinstance(x.get(key),str) or not x.get(key) for key in PACKAGE_FIELDS)
                   or re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*",x["name"]) is None
                   or re.fullmatch(r"github\.com/[^/]+/[^/]+",x["normalized_remote"]) is None
                   or not Path(x["build_root"]).is_absolute()
                   or Path(x["build_root"])!=Path(x["build_root"]).resolve(strict=False)
                   or not Path(x["facade"]).is_absolute()
                   or Path(x["facade"])!=Path(receipt.get("repo", ""))/"proofs/.lake/packages"/x["name"]
                   for x in packages)
            or len({x.get("name") for x in packages})!=len(packages)
            or len({x.get("normalized_remote") for x in packages})!=len(packages)
            or any(not isinstance(receipt.get(key),str) or not receipt.get(key) for key in scalar_paths)
            or any(not Path(receipt[key]).is_absolute()
                   or Path(receipt[key])!=Path(receipt[key]).resolve(strict=False) for key in scalar_paths)):
        raise ArchiveError("overlay receipt exact contract mismatch")
    return {"entry_count":count,"manifest_sha256":receipt["manifest_sha256"],
            "overlay_identity_sha256":receipt["overlay_identity_sha256"],
            "receipt_sha256":sha256_file(publication/"receipt.json")}

def source_members(publication):
    rows=[]; inodes=set()
    for path in publication.rglob("*"):
        relative=path.relative_to(publication).as_posix()
        if path.is_symlink(): raise ArchiveError("publication contains symlink")
        if path.is_dir(): rows.append((relative,path,True))
        elif path.is_file():
            stat=path.stat(); inode=(stat.st_dev,stat.st_ino)
            if stat.st_nlink!=1 or inode in inodes: raise ArchiveError("publication contains hardlink/alias")
            inodes.add(inode); rows.append((relative,path,False))
        else: raise ArchiveError("publication contains special entry")
    rows.sort(key=lambda x:x[0])
    return rows

def write_tar(publication,tar_path):
    with tarfile.open(tar_path,"w",format=tarfile.GNU_FORMAT) as archive:
        for name,path,is_dir in source_members(publication):
            info=tarfile.TarInfo(name); info.uid=0; info.gid=0; info.uname=""; info.gname=""; info.mtime=0
            if is_dir:
                info.type=tarfile.DIRTYPE; info.mode=0o755; info.size=0; archive.addfile(info)
            else:
                info.type=tarfile.REGTYPE; info.mode=0o644; info.size=path.stat().st_size
                with path.open("rb") as stream: archive.addfile(info,stream)

def run(argv,label):
    result=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if result.returncode!=0 or result.stdout or result.stderr: raise ArchiveError(f"{label} command failed/malformed")

def expected_member_names(publication): return [name for name,_,_ in source_members(publication)]

def unpack_verify(archive,zstd_path,zstd_sha256):
    require(archive,sha256_file(archive),"archive"); require(zstd_path,zstd_sha256,"zstd")
    with tempfile.TemporaryDirectory(prefix=".h1-overlay-archive-verify-",dir=archive.parent) as raw:
        root=Path(raw); tar_path=root/"archive.tar"; extracted=root/"publication"; extracted.mkdir()
        run([str(zstd_path),*ZSTD_DECOMPRESS,str(archive),"-o",str(tar_path)],"zstd decompress")
        with tarfile.open(tar_path,"r:") as stream:
            members=stream.getmembers(); names=[]
            for member in members:
                pure=PurePosixPath(member.name)
                if (not member.name or "\\" in member.name or pure.is_absolute()
                        or pure.as_posix()!=member.name or any(x in ("",".","..") for x in pure.parts)
                        or member.uid!=0 or member.gid!=0 or member.uname!="" or member.gname!=""
                        or member.mtime!=0 or member.mode!=(0o755 if member.isdir() else 0o644)
                        or not (member.isdir() or member.isreg()) or member.linkname):
                    raise ArchiveError("archive member metadata/path/link contract mismatch")
                if member.name in names: raise ArchiveError("archive duplicate member")
                names.append(member.name); destination=extracted.joinpath(*pure.parts)
                if member.isdir(): destination.mkdir(parents=True,exist_ok=False)
                else:
                    destination.parent.mkdir(parents=True,exist_ok=True); source=stream.extractfile(member)
                    if source is None: raise ArchiveError("archive regular member missing payload")
                    with destination.open("xb") as output:
                        while block:=source.read(1<<20): output.write(block)
            if names!=sorted(names): raise ArchiveError("archive member order mismatch")
        identity=validate_publication(extracted)
        if names!=expected_member_names(extracted): raise ArchiveError("archive member census mismatch")
        return identity

def result_identity(identity,archive,zstd_path,zstd_sha256,archive_bytes=None,archive_sha256=None):
    producer=Path(__file__).resolve()
    return {**identity,"archive_bytes":archive.stat().st_size if archive_bytes is None else archive_bytes,
      "archive_sha256":sha256_file(archive) if archive_sha256 is None else archive_sha256,
      "producer_sha256":sha256_file(producer),
      "zstd_argv":[str(zstd_path),*ZSTD_COMPRESS,"{tar}","-o","{archive}"],
      "schema":ARCHIVE_SCHEMA,"zstd_path":str(zstd_path),"zstd_sha256":zstd_sha256}

def build(publication,output,zstd_path,zstd_sha256,before_link=None,after_link=None,before_result=None):
    safe(output,"archive output",absent=True); require(zstd_path,zstd_sha256,"zstd")
    identity=validate_publication(publication)
    source_pins={str(path):sha256_file(path) for _,path,is_dir in source_members(publication) if not is_dir}
    with tempfile.TemporaryDirectory(prefix=".h1-overlay-archive-",dir=output.parent) as raw:
        stage=Path(raw); tar_path=stage/"publication.tar"; compressed=stage/"publication.tar.zst"
        write_tar(publication,tar_path)
        argv=[str(zstd_path),*ZSTD_COMPRESS,str(tar_path),"-o",str(compressed)]; run(argv,"zstd compress")
        for text,pin in source_pins.items(): require(Path(text),pin,"publication input drift")
        if validate_publication(publication)!=identity: raise ArchiveError("publication identity drift")
        if unpack_verify(compressed,zstd_path,zstd_sha256)!=identity: raise ArchiveError("archive readback identity mismatch")
        stage_sha=sha256_file(compressed); stage_bytes=compressed.stat().st_size
        with compressed.open("rb") as stream: os.fsync(stream.fileno())
        for text,pin in source_pins.items(): require(Path(text),pin,"publication input drift")
        if validate_publication(publication)!=identity: raise ArchiveError("publication identity drift")
        if before_link: before_link()
        for text,pin in source_pins.items(): require(Path(text),pin,"publication input drift")
        if validate_publication(publication)!=identity: raise ArchiveError("publication identity drift")
        try: os.link(compressed,output)
        except FileExistsError as error: raise ArchiveError("archive output appeared") from error
        fd=os.open(output.parent,os.O_RDONLY)
        try: os.fsync(fd)
        finally: os.close(fd)
        if after_link: after_link()
        try:
            def owned():
                return (output.exists() and os.path.samestat(output.stat(),compressed.stat())
                        and output.stat().st_size==stage_bytes and sha256_file(output)==stage_sha)
            if not owned():
                raise ArchiveError("published archive ownership/identity drift")
            if unpack_verify(output,zstd_path,zstd_sha256)!=identity: raise ArchiveError("published archive drift")
            if not owned():
                raise ArchiveError("published archive ownership/identity drift")
            if before_result: before_result()
            if not owned(): raise ArchiveError("published archive ownership/identity drift")
            result=result_identity(identity,compressed,zstd_path,zstd_sha256,stage_bytes,stage_sha)
            if not owned(): raise ArchiveError("published archive ownership/identity drift")
        except BaseException:
            try:
                if output.exists() and os.path.samestat(output.stat(),compressed.stat()): output.unlink()
            finally:
                fd=os.open(output.parent,os.O_RDONLY)
                try: os.fsync(fd)
                finally: os.close(fd)
            raise
        return result

def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--publication",type=Path)
    parser.add_argument("--output",type=Path); parser.add_argument("--verify",type=Path)
    parser.add_argument("--zstd-path",type=Path,required=True); parser.add_argument("--zstd-sha256",required=True)
    args=parser.parse_args()
    try:
        if args.verify:
            if args.publication or args.output: raise ArchiveError("verify/build arguments mixed")
            result=result_identity(unpack_verify(args.verify,args.zstd_path,args.zstd_sha256),
                                   args.verify,args.zstd_path,args.zstd_sha256)
        else:
            if args.publication is None or args.output is None: raise ArchiveError("build inputs incomplete")
            result=build(args.publication,args.output,args.zstd_path,args.zstd_sha256)
        print(canonical(result).decode("ascii"),end=""); return 0
    except (OSError,tarfile.TarError,ArchiveError) as error:
        print(f"ARCHIVE_ERROR: {error}"); return 2

if __name__=="__main__": raise SystemExit(main())
