#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using U = std::uint64_t;

// Exact successive-prime mixed-radix addition. No floating-point arithmetic.
bool carry_free(std::vector<U> v) {
  constexpr unsigned bases[] = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61};
  for (unsigned b : bases) {
    unsigned sum = 0;
    bool nonzero = false;
    for (U &a : v) { sum += a % b; a /= b; nonzero |= (a != 0); }
    if (sum >= b) return false;
    if (!nonzero) return true;
  }
  throw "insufficient digit bases";
}

int main() {
  const auto started = std::chrono::steady_clock::now();
  if (!carry_free({2343,1562,426,66})) return 2; // Exact source example n=4686.
  constexpr unsigned B = 20000;
  std::vector<bool> isprime(B+1,true); isprime[0]=isprime[1]=false;
  for (unsigned p=2;p*p<=B;++p) if(isprime[p])
    for(unsigned q=p*p;q<=B;q+=p)isprime[q]=false;
  std::vector<U> ps;
  for(unsigned p=7;p<=B;++p) if(isprime[p]&&p%5==1)ps.push_back(p);
  U tested=0;
  for(unsigned i=0;i<ps.size();++i)for(unsigned j=i+1;j<ps.size();++j)
    for(unsigned k=j+1;k<ps.size();++k){
      U p=ps[i],q=ps[j],r=ps[k];
      if((p%3)*(q%3)*(r%3)%3!=1)continue;
      ++tested;
      if(carry_free({3*p*q*r,2*p*q*r,6*q*r,6*p*r,6*p*q})){
        U n=6*p*q*r;
        auto sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
        std::cout<<"{\"status\":\"counterexample_candidate\",\"n\":"<<n
          <<",\"prime_factors\":[2,3,"<<p<<","<<q<<","<<r
          <<"],\"tested\":"<<tested<<",\"prime_bound\":"<<B<<",\"seconds\":"<<sec<<"}\n";
        return 0;
      }
    }
  auto sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
  std::cout<<"{\"status\":\"no_counterexample_in_fixed_reduced_search\",\"tested\":"<<tested
    <<",\"prime_bound\":"<<B<<",\"eligible_primes\":"<<ps.size()<<",\"seconds\":"<<sec<<"}\n";
}
