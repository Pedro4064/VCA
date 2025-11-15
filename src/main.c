#include "filter.h"
#include <string.h>


/*@ requires \valid(dest);
    assigns *dest \from \nothing;
    ensures \is_finite(*dest) && 0.0f <= *dest <= 3300.0f;
*/
extern void rtos_sample_adc(float* dest);

void rtos_burst_sample_adc(float* raw_data_buffer, int n_samples){
  //@ loop unroll n_samples;
  for (int i = 0; i < n_samples; i++) rtos_sample_adc(&raw_data_buffer[i]);
}

int main(void) {
  float raw_data[50]; 
  float filtered_data[41]; 
  memset(raw_data, 0, sizeof(raw_data));
  memset(filtered_data, 0, sizeof(filtered_data));

  rtos_burst_sample_adc(raw_data, 50);
  /*@ assert \forall integer i; 0 <= i < 50 ==> \is_finite(raw_data[i]);*/

  f_moving_average_filter(raw_data, 50, filtered_data, 41, 10);
}