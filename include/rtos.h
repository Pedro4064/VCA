/*@ requires \valid(dest);
    assigns *dest \from ;
    ensures \is_finite(*dest) && 0.0f <= *dest <= 3300.0f;
*/
extern void sample_adc(float* data_target);