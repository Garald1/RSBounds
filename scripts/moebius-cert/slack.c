// For segments of size S aligned at multiples of S (L >= L0), check max|M| over segment <= B(L) = isqrt(326041 L / 1e6).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
static int64_t isqrt_floor(__int128 x){ int64_t r=(int64_t)sqrtl((long double)x); while((__int128)r*r>x) r--; while((__int128)(r+1)*(r+1)<=x) r++; return r; }
int main(int argc,char**argv){
  int64_t N=1000000000LL; int64_t S=atoll(argv[1]); int64_t L0=atoll(argv[2]);
  int64_t R=31700; char*isc=calloc(R+1,1); int64_t*pr=malloc(8*R); int np=0;
  for(int64_t i=2;i<=R;i++) if(!isc[i]){pr[np++]=i; for(int64_t j=i*i;j<=R;j+=i) isc[j]=1;}
  const int64_t SEG=1<<20; int64_t*rem=malloc(8*SEG); int8_t*mu=malloc(SEG);
  int64_t M=0, segL=-1, segmax=0, fails=0; double minslack=1e9; int64_t minslackL=0;
  for(int64_t lo=1;lo<=N;lo+=SEG){ int64_t hi=lo+SEG-1; if(hi>N)hi=N; int64_t len=hi-lo+1;
    for(int64_t i=0;i<len;i++){rem[i]=lo+i;mu[i]=1;}
    for(int k=0;k<np;k++){int64_t p=pr[k]; if(p*p>hi)break; int64_t s=((lo+p-1)/p)*p;
      for(int64_t m=s;m<=hi;m+=p){rem[m-lo]/=p;mu[m-lo]=-mu[m-lo];}
      int64_t p2=p*p; s=((lo+p2-1)/p2)*p2; for(int64_t m=s;m<=hi;m+=p2)mu[m-lo]=0;}
    for(int64_t i=0;i<len;i++){int64_t n=lo+i; int m=mu[i]; if(m&&rem[i]>1)m=-m; M+=m;
      if(n>=L0){ int64_t L=(n/S)*S; if(L!=segL){ if(segL>=0){ int64_t B=isqrt_floor(((__int128)326041*segL)/1000000); double sl=(double)(B-segmax); if(segmax>B){fails++; if(fails<5)printf("FAIL L=%lld max=%lld B=%lld\n",(long long)segL,(long long)segmax,(long long)B);} if(sl<minslack){minslack=sl;minslackL=segL;} } segL=L; segmax=0; }
        int64_t a=M<0?-M:M; if(a>segmax)segmax=a; } } }
  printf("S=%lld L0=%lld fails=%lld minslack=%.0f at L=%lld\n",(long long)S,(long long)L0,(long long)fails,minslack,(long long)minslackL);
}
