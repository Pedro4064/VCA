#include "filter.h"
// #include "rtos.h"
#include <string.h>

/*@ 
  requires \valid(raw_data + (0 .. 49));
  assigns raw_data[0 .. 49] \from \nothing;
  ensures \forall integer i; 0 <= i < 50 ==>  \is_finite(raw_data[i]) && 0.0f<=raw_data[i]<=3300.0f;
  ensures \is_finite(raw_data[0]) && 0.0f<=raw_data[0]<=3300.0f;
  ensures \is_finite(raw_data[1]) && 0.0f<=raw_data[1]<=3300.0f;
  ensures \is_finite(raw_data[2]) && 0.0f<=raw_data[2]<=3300.0f;
  ensures \is_finite(raw_data[3]) && 0.0f<=raw_data[3]<=3300.0f;
  ensures \is_finite(raw_data[4]) && 0.0f<=raw_data[4]<=3300.0f;
  ensures \is_finite(raw_data[5]) && 0.0f<=raw_data[5]<=3300.0f;
  ensures \is_finite(raw_data[6]) && 0.0f<=raw_data[6]<=3300.0f;
  ensures \is_finite(raw_data[7]) && 0.0f<=raw_data[7]<=3300.0f;
  ensures \is_finite(raw_data[8]) && 0.0f<=raw_data[8]<=3300.0f;
  ensures \is_finite(raw_data[9]) && 0.0f<=raw_data[9]<=3300.0f;
  ensures \is_finite(raw_data[10]) && 0.0f<=raw_data[10]<=3300.0f;
  ensures \is_finite(raw_data[11]) && 0.0f<=raw_data[11]<=3300.0f;
  ensures \is_finite(raw_data[12]) && 0.0f<=raw_data[12]<=3300.0f;
  ensures \is_finite(raw_data[13]) && 0.0f<=raw_data[13]<=3300.0f;
  ensures \is_finite(raw_data[14]) && 0.0f<=raw_data[14]<=3300.0f;
  ensures \is_finite(raw_data[15]) && 0.0f<=raw_data[15]<=3300.0f;
  ensures \is_finite(raw_data[16]) && 0.0f<=raw_data[16]<=3300.0f;
  ensures \is_finite(raw_data[17]) && 0.0f<=raw_data[17]<=3300.0f;
  ensures \is_finite(raw_data[18]) && 0.0f<=raw_data[18]<=3300.0f;
  ensures \is_finite(raw_data[19]) && 0.0f<=raw_data[19]<=3300.0f;
  ensures \is_finite(raw_data[20]) && 0.0f<=raw_data[20]<=3300.0f;
  ensures \is_finite(raw_data[21]) && 0.0f<=raw_data[21]<=3300.0f;
  ensures \is_finite(raw_data[22]) && 0.0f<=raw_data[22]<=3300.0f;
  ensures \is_finite(raw_data[23]) && 0.0f<=raw_data[23]<=3300.0f;
  ensures \is_finite(raw_data[24]) && 0.0f<=raw_data[24]<=3300.0f;
  ensures \is_finite(raw_data[25]) && 0.0f<=raw_data[25]<=3300.0f;
  ensures \is_finite(raw_data[26]) && 0.0f<=raw_data[26]<=3300.0f;
  ensures \is_finite(raw_data[27]) && 0.0f<=raw_data[27]<=3300.0f;
  ensures \is_finite(raw_data[28]) && 0.0f<=raw_data[28]<=3300.0f;
  ensures \is_finite(raw_data[29]) && 0.0f<=raw_data[29]<=3300.0f;
  ensures \is_finite(raw_data[30]) && 0.0f<=raw_data[30]<=3300.0f;
  ensures \is_finite(raw_data[31]) && 0.0f<=raw_data[31]<=3300.0f;
  ensures \is_finite(raw_data[32]) && 0.0f<=raw_data[32]<=3300.0f;
  ensures \is_finite(raw_data[33]) && 0.0f<=raw_data[33]<=3300.0f;
  ensures \is_finite(raw_data[34]) && 0.0f<=raw_data[34]<=3300.0f;
  ensures \is_finite(raw_data[35]) && 0.0f<=raw_data[35]<=3300.0f;
  ensures \is_finite(raw_data[36]) && 0.0f<=raw_data[36]<=3300.0f;
  ensures \is_finite(raw_data[37]) && 0.0f<=raw_data[37]<=3300.0f;
  ensures \is_finite(raw_data[38]) && 0.0f<=raw_data[38]<=3300.0f;
  ensures \is_finite(raw_data[39]) && 0.0f<=raw_data[39]<=3300.0f;
  ensures \is_finite(raw_data[40]) && 0.0f<=raw_data[40]<=3300.0f;
  ensures \is_finite(raw_data[41]) && 0.0f<=raw_data[41]<=3300.0f;
  ensures \is_finite(raw_data[42]) && 0.0f<=raw_data[42]<=3300.0f;
  ensures \is_finite(raw_data[43]) && 0.0f<=raw_data[43]<=3300.0f;
  ensures \is_finite(raw_data[44]) && 0.0f<=raw_data[44]<=3300.0f;
  ensures \is_finite(raw_data[45]) && 0.0f<=raw_data[45]<=3300.0f;
  ensures \is_finite(raw_data[46]) && 0.0f<=raw_data[46]<=3300.0f;
  ensures \is_finite(raw_data[47]) && 0.0f<=raw_data[47]<=3300.0f;
  ensures \is_finite(raw_data[48]) && 0.0f<=raw_data[48]<=3300.0f;
  ensures \is_finite(raw_data[49]) && 0.0f<=raw_data[49]<=3300.0f;
  ensures \is_finite(raw_data[50]) && 0.0f<=raw_data[50]<=3300.0f;
*/
void burst_sample_adc(float raw_data[50]);

int main(void) {
  float raw_data[50]; 
  float filtered_data[41]; 
  memset(raw_data, 0, sizeof(raw_data));
  memset(filtered_data, 0, sizeof(filtered_data));

  burst_sample_adc(raw_data);
  /*@ assert \forall integer i; 0 <= i < 50 ==> \is_finite(raw_data[i]);*/
  f_moving_average_filter(raw_data, 50, filtered_data, 41, 10);
}