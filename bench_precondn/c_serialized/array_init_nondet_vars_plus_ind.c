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
    int x;
    int y;
    __VERIFIER_assume(x<100000 && x > -100000);
    __VERIFIER_assume(y<100000 && y > -100000);
    __VERIFIER_assume(x>y);
    a[i]=y;
    b[i]=x;
  }

  for(i=0;i<N;i++){
    c[i]=a[i]-b[i];
  }

  for(i=1;i<N;i++)
    __VERIFIER_assert(c[i] < 0);
}

