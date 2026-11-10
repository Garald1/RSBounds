import resource, subprocess, sys, time
t=time.time(); r=subprocess.run(sys.argv[1:]); dt=time.time()-t
u=resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"[rtime] wall={dt:.2f}s user={u.ru_utime:.2f}s sys={u.ru_stime:.2f}s maxrss={u.ru_maxrss/1024:.0f}MB rc={r.returncode}", file=sys.stderr)
sys.exit(r.returncode)
