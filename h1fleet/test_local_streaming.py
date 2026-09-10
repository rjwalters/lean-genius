import unittest,tempfile,hashlib,threading,os
from pathlib import Path
from unittest.mock import patch
from concurrent.futures import ThreadPoolExecutor
from replay_common import LocalObjectStore,ReplayError

class StreamingTest(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
  self.root=Path(self.tmp.name);self.store=LocalObjectStore(self.root/'store')
  self.source=self.root/'source';self.data=b'abcde'*(1024*1024);self.source.write_bytes(self.data)
 def test_streams_without_whole_file_reads(self):
  target=self.root/'target'
  with patch.object(Path,'read_bytes',side_effect=AssertionError('whole-file read')):
   info=self.store.put_immutable('leaf',self.source,{'purpose':'test'})
   got=self.store.download('leaf',target)
  self.assertEqual(info.sha256,hashlib.sha256(self.data).hexdigest())
  self.assertEqual(got.sha256,info.sha256);self.assertEqual(target.read_bytes(),self.data)
 def test_identical_resume_and_collision(self):
  first=self.store.put_immutable('leaf',self.source,{})
  self.assertEqual(first,self.store.put_immutable('leaf',self.source,{}))
  self.source.write_bytes(b'different')
  with self.assertRaises(ReplayError):self.store.put_immutable('leaf',self.source,{})
  self.assertEqual(self.store.head('leaf').sha256,first.sha256)
  self.assertFalse(list(self.store.objects.rglob('.copy-*')))
 def test_hidden_head_digest_still_verifies_download(self):
  self.store.put_immutable('leaf',self.source,{'simulate-head-without-sha256':'true'})
  self.assertIsNone(self.store.head('leaf').sha256)
  got=self.store.download('leaf',self.root/'target')
  self.assertEqual(got.sha256,hashlib.sha256(self.data).hexdigest())
 def test_copy_failure_preserves_download_destination_and_cleans_stage(self):
  self.store.put_immutable('leaf',self.source,{})
  target=self.root/'target';target.write_bytes(b'previous')
  with patch('replay_common.os.fsync',side_effect=OSError('disk error')):
   with self.assertRaises(OSError):self.store.download('leaf',target)
  self.assertEqual(target.read_bytes(),b'previous');self.assertFalse(list(self.root.glob('.copy-*')))
 def test_concurrent_different_publishers_never_overwrite(self):
  other=self.root/'other';other.write_bytes(b'other')
  barrier=threading.Barrier(2);original=os.link
  def simultaneous(src,dst):barrier.wait(timeout=5);return original(src,dst)
  def publish(src):
   try:return self.store.put_immutable('same',src,{})
   except ReplayError:return None
  with patch('replay_common.os.link',side_effect=simultaneous),ThreadPoolExecutor(2) as pool:
   results=list(pool.map(publish,[self.source,other]))
  accepted=[r for r in results if r is not None];self.assertEqual(len(accepted),1)
  self.assertEqual(self.store.head('same'),accepted[0]);self.assertFalse(list(self.store.objects.rglob('.copy-*')))
 def test_source_mutation_during_copy_rejected_before_publication(self):
  original=os.fsync
  def mutate(fd):
   original(fd)
   self.source.write_bytes(b'changed')
  with patch('replay_common.os.fsync',side_effect=mutate):
   with self.assertRaisesRegex(ReplayError,'changed during'):self.store.put_immutable('leaf',self.source,{})
  self.assertFalse((self.store.objects/'leaf').exists());self.assertFalse(list(self.store.objects.rglob('.copy-*')))
 def test_metadata_write_failure_leaves_incomplete_key_fail_closed(self):
  with patch('replay_common.atomic_write',side_effect=OSError('metadata disk error')):
   with self.assertRaises(OSError):self.store.put_immutable('leaf',self.source,{})
  self.assertTrue((self.store.objects/'leaf').is_file())
  self.assertFalse((self.store.meta/'leaf.json').exists())
  self.assertFalse(list(self.store.objects.rglob('.copy-*')))
  with self.assertRaisesRegex(ReplayError,'missing object'):
   self.store.put_immutable('leaf',self.source,{})
if __name__=='__main__':unittest.main()
