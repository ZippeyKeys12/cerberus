#include "linux.h"
int main(void)
{
int x = 0;
int y = 0;

int T1_r1;
{-{
{ WRITE_ONCE(x,2);
smp_wmb();
WRITE_ONCE(y,1); }
|||
{ T1_r1 = READ_ONCE(y);
smp_mb();
WRITE_ONCE(x,1); }
}-};
 assert(!(x == 2 && T1_r1 == 1));
}
