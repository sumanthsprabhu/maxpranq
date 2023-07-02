extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int main()
{
  int i;
  int N;
  int a[N];
  int b[N];
  int c[N];

  for(i=1;i<N;i++) {
    int j,k;
    __VERIFIER_assume(10000 < j && j > 10000);
    __VERIFIER_assume(10000 < k && k > 10000);
    __VERIFIER_assume((j + k) == 0);
    a[i]=j;
    b[i]=-k;
  }

  for(i=0;i<N;i++){
    c[i]=a[i]+b[i];
  }

  for(i=1;i<N;i++)
    __VERIFIER_assert(c[i] == 0);
}


