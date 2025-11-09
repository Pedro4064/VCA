#include <limits.h>
#include "main.h"



/*@
    predicate f_valid_array_r(float* array, unsigned int length) =
        \valid_read(array+(0..length-1)) && 0<=length<=INT_MAX;

    predicate f_valid_array_rw(float* array, unsigned int length) =
        \valid(array+(0..length-1)) && 0<=length<=INT_MAX;

*/





/*@
    logic float f_sum_to_index(float* values, integer index) = 
        (index<0)? (float)(0): (float)(values[index]+(float)f_sum_to_index(values, index-1));

    logic float f_sum(float* values, integer length) = (float)(f_sum_to_index(values, length-1));
*/

/*@
    requires valid_array: \valid_read(values+(0..length-1));
    requires valid_length: 0<=length<=50;
    requires \forall integer i; 0 <= i < length ==> \is_finite(values[i]);

    assigns \nothing;
*/
float f_sum(float* values, int length){
    float result = 0.0f;
    for(int i=0; i<length; i++)
        result+=values[i];
    return result;
}


/*@
    logic float f_average(float* array, integer n) = (float)(f_sum(array, n)/n);
    lemma f_div_mul: \forall float a, b, m  ; m > 0.0f ==> 0.0f <= a <= (float)(b * m) ==> 0.0f <= (float)(a / m) <= b ;
*/


/*@
    requires valid_window_size: 0 < window_size <= raw_data_length <= 50;
    requires valid_buffer_size: filtered_data_length == raw_data_length - window_size + 1;
    requires valid_value_range: \forall integer i; 0 <= i < raw_data_length ==>  0.0f <= raw_data[i] <= (float)(MAX_VOLTAGE);
    requires mem_separation: \separated(raw_data+(0..raw_data_length-1), filtered_data+(0..filtered_data_length-1));
    requires valid_pointers: f_valid_array_r(raw_data, raw_data_length) &&
                             f_valid_array_rw(filtered_data, filtered_data_length);

    assigns filtered_data[0..filtered_data_length-1];
*/
void f_moving_average_filter(float* raw_data, unsigned int raw_data_length,
                          float* filtered_data, unsigned int filtered_data_length,
                          unsigned int window_size){
    
    for (unsigned int i = 0; i < filtered_data_length; i++) {
        filtered_data[i] = f_sum(raw_data+i, window_size)/window_size;
    }
}

