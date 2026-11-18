import numpy as np, time

RT='rtable_1M.npy'
r=np.load(RT); NF=len(r)
KMAX=int(r.max())
print('k max couvert: %d'%KMAX, flush=True)

P=np.ones(2*NF,bool); P[0]=P[1]=False
for i in range(2,int((2*NF)**.5)+1):
    if P[i]: P[i*i::i]=False

def rays(m):
    return np.flatnonzero(P[m-1:1:-1]&P[m+1:2*m-1])+1

# mu_c[k] = premier m de classe c avec r(m)>=k  (fonction en escaliers)
mu=np.zeros((3,KMAX+1),np.int64)
maxR=np.zeros(3,np.int64)
for m in range(4,NF):
    c=m%3; rm=int(r[m])
    if rm>maxR[c]:
        mu[c,maxR[c]+1:rm+1]=m
        maxR[c]=rm
klive=min(KMAX,int(maxR.max()))

# pour chaque mu distinct : precalcul
#  classe chargee : echappe ssi 2m-3 premier ET max r(enfants-pont)>=k
#  classe 0       : echappe ssi M(m)=max r(enfants)>=k  (uniquement si non min global)
cache={}
def bridge_max_r(m):
    """max r(n) sur les enfants issus du pont (a, m-3)."""
    if not P[2*m-3]: return -1
    if m in cache: return cache[m][0]
    T=rays(m); a=T[T!=m-3]
    n1=m-(m-3-a)//2; n2=m-(a+m-3)//2
    ns=np.concatenate([n1,n2]); ns=ns[(ns>=4)&(ns<m)]
    br=int(r[ns].max()) if len(ns) else 0
    Mfull=None
    cache[m]=[br,Mfull]
    return br
def full_max_r(m):
    if m in cache and cache[m][1] is not None: return cache[m][1]
    T=rays(m); M=0
    for i in range(len(T)):
        a=T[i]; b=T[i+1:]
        for v in ((b-a)//2,(a+b)//2):
            n=m-v; ok=(n>=4)&(n<m)
            if ok.any(): M=max(M,int(r[n[ok]].max()))
    if m in cache: cache[m][1]=M
    else: cache[m]=[None,M]
    return M

hist={1:0,2:0,3:0,4:0,5:0}
derniers2=[]; detail2=[]; liste5=[]
for k in range(1,klive+1):
    m0,m1,m2=mu[0,k],mu[1,k],mu[2,k]
    pits=0
    # mu0
    if m0:
        if m0==min([x for x in (m0,m1,m2) if x]):
            pits+=1
        elif full_max_r(m0)<k:
            pits+=1
    for mc in (m1,m2):
        if not mc: continue
        # min de sa classe : enfants meme classe <mc non vitaux ; echappe ssi pont
        if bridge_max_r(mc)<k: pits+=1
    hist[pits]=hist.get(pits,0)+1
    if pits!=3: derniers2.append(k)
    if pits==5: liste5.append(k)

print('compte puits par k:',{p:c for p,c in sorted(hist.items())})
print('k=1..5 puits?', liste5[:5])
d=[k for k in derniers2 if k!=1]
print('k avec #puits !=3 :', derniers2[:30])
print('dernier k a 2 puits :', max([k for k in derniers2 if hist and True] or [0]))
# rechutes : k>64 avec pits==2
rech=[k for k in derniers2 if k>=3 and k<klive]
print('rechutes 2 puits :', rech[-10:] if rech else 'aucune', ' total=%d'%len(rech))
print('k a 4+ puits :', [k for k in range(1,klive+1) if False])
for k in sorted(set(derniers2)):
    m0,m1,m2=mu[0,k],mu[1,k],mu[2,k]
    print('k=%d mu=(%d,%d,%d)'%(k,m0,m1,m2))
