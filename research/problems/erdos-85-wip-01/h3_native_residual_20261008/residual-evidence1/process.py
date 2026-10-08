"""Cooperative process-group cancellation for the bounded residual workers."""
import hashlib,os,signal,subprocess,time
from datetime import datetime,timezone

def run_child(command,log_path,cap,deadline,stop_path,stop_event):
    if cap<=0:raise ValueError('Positive child cap required')
    started=time.monotonic();started_utc=datetime.now(timezone.utc).isoformat();effective=min(cap,max(0,deadline-started))
    reason='STOP' if stop_event.is_set() or stop_path.exists() else 'BUDGET_STOP' if effective<=0 else None
    if reason:
        stop_event.set()
        return {'command':command,'launched':False,'returncode':None,'stop_reason':reason,
                'timeout_seconds':cap,'effective_timeout_seconds':effective,'elapsed_seconds':0}
    child=None
    try:
        with log_path.open('xb') as output:
            child=subprocess.Popen(command,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
            while child.poll() is None:
                if stop_event.is_set() or stop_path.exists():reason='STOP'
                elif time.monotonic()-started>=effective:
                    reason='TIMEOUT' if effective==cap else 'BUDGET_STOP'
                if reason:
                    stop_event.set();break
                try:child.wait(timeout=min(.1,max(.001,effective-(time.monotonic()-started))))
                except subprocess.TimeoutExpired:pass
            if reason:
                try:os.killpg(child.pid,signal.SIGKILL)
                except ProcessLookupError:pass
            child.wait()
    except BaseException:
        stop_event.set()
        if child is not None:
            try:os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            child.wait()
        raise
    if child.returncode!=0:stop_event.set()
    return {'command':command,'launched':True,'pid':child.pid,'returncode':child.returncode,'stop_reason':reason,
            'timeout_seconds':cap,'effective_timeout_seconds':effective,'elapsed_seconds':time.monotonic()-started,
            'started_utc':started_utc,'finished_utc':datetime.now(timezone.utc).isoformat(),
            'log_sha256':hashlib.sha256(log_path.read_bytes()).hexdigest()}
