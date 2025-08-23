#include <limits.h>

#define MAX_VOLTAGE 3300

/*@
    logic integer sum_to_index(int* values, integer index) =
        (index < 0)? 0:
                      values[index] + sum_to_index(values, index - 1);

    logic integer sum(int* values, integer length) =
        sum_to_index(values, length-1);
*/

/*@
    requires valid_array: \valid_read(values+(0..length-1));
    requires valid_length: 0<=length<=50;
    requires valid_range: \forall integer i; 0<= i < length ==> 0<=values[i]<=MAX_VOLTAGE;

    assigns \nothing;

    ensures \result == sum(values, length);
 */
int sum(int *values, unsigned int length) {
    int result = 0;

    /*@
        loop invariant 0 <= i <= length;
        loop invariant result == (i == 0 ? 0 : sum_to_index(values, i - 1));
        loop invariant result <= i * MAX_VOLTAGE;
        loop assigns result, i;
        loop variant length - i;
    */
    for (int i = 0; i < length; i++) {
        result += values[i];
    }

    return result;
}

/*@
    predicate valid_array_r(int* array, unsigned int length) =
        \valid_read(array+(0..length-1)) && 0<=length<=INT_MAX;

    predicate valid_array_rw(int* array, unsigned int length) =
        \valid(array+(0..length-1)) && 0<=length<=INT_MAX;

    logic integer average(int* array, integer n) = sum(array, n)/n;

*/

/*@ ghost
  /@ requires \forall integer i ; 0 <= i < len ==> 0 <= array[i] <= MAX_VOLTAGE ;
      assigns \nothing ;
      ensures 0 <= sum(array, len) <= len * MAX_VOLTAGE ;
  @/
  void lemma_bound_sum(int* array, unsigned len){
    /@ loop invariant 0 <= i <= len ;
       loop invariant 0 <= sum(array, i) <= i * MAX_VOLTAGE;
       loop assigns i ;
       loop variant len - i ;
    @/
    for(unsigned i = 0 ; i < len ; i++);
  }
*/


//@ lemma div_mul: \forall integer a, b, m  ; m > 0 ==> 0 <= a <= b * m ==> 0 <= a / m <= b ;

/*@
    requires valid_window_size: 0 < window_size <= raw_data_length <= 50;
    requires valid_buffer_size: filtered_data_length == raw_data_length - window_size + 1;
    requires valid_value_range: \forall integer i; 0 <= i < raw_data_length ==>  0 <= raw_data[i] <= MAX_VOLTAGE;
    requires mem_separation: \separated(raw_data+(0..raw_data_length-1), filtered_data+(0..filtered_data_length-1));
    requires valid_pointers: valid_array_r(raw_data, raw_data_length) &&
                             valid_array_rw(filtered_data, filtered_data_length);

    assigns filtered_data[0..filtered_data_length-1];

    ensures \forall integer i; 0<= i < filtered_data_length ==> filtered_data[i] ==  average(raw_data+i, window_size);
*/
void moving_average_filter(int* raw_data, unsigned int raw_data_length,
                          int* filtered_data, unsigned int filtered_data_length,
                          unsigned int window_size){
    /*@
        loop invariant 0 <= i <= filtered_data_length;
        loop invariant \forall integer k; 0 <= k < i ==> filtered_data[k]==average(raw_data+k, window_size);
        loop invariant \forall integer k; 0 <= k < i ==> 0 <= filtered_data[k] <= MAX_VOLTAGE;

        loop assigns i, filtered_data[0..filtered_data_length-1];

        loop variant filtered_data_length - i;
    */
    for (unsigned int i = 0; i < filtered_data_length; i++) {
        //@ ghost top_entry: ;
        //@ ghost lemma_bound_sum(raw_data+i, window_size);
        filtered_data[i] = sum(raw_data+i, window_size)/window_size;
        /*@ assert
            \forall integer k, x ;
                0 <= k < i ==>
                0 <= x < window_size ==>
                    \at((raw_data+k)[x], top_entry) == (raw_data+k)[x];
        */

        /*@ ghost
            /@ loop invariant 0 <= k <= i+1 ;
               loop invariant
                   \forall integer j ; 0 <= j < k ==>
                       sum(raw_data+j, window_size) ==
                       sum{top_entry}(raw_data+j, window_size) ;
               loop assigns k ;
               loop variant (i + 1) - k ;
            @/
            for(unsigned k = 0 ; k <= i ; k++){
                /@ loop invariant 0 <= e <= window_size ;
                   loop invariant sum(raw_data+k, e) == sum{top_entry}(raw_data+k, e);
                   loop assigns e;
                   loop variant window_size - e ;
                @/
                for(unsigned e = 0 ; e < window_size ; e++);
            }
        */
        /*@ assert
            \forall integer k ;
                0 <= k <= i ==>
                    sum(raw_data+k, window_size) ==
                    sum{LoopCurrent}(raw_data+k, window_size) ;
        */
    }
}
