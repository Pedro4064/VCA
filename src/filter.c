#include <limits.h>

/*@
    ensures \result == a+b;
*/
int add(int a, int b){
    return a+b;
}
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

    assigns \nothing;

    ensures \result == sum(values, length);
 */
int sum(int* values, int length){
    int result = 0;
      /*@
        loop invariant 0 <= i <= length;
        loop invariant result == (i == 0 ? 0 : sum_to_index(values, i - 1));
        loop assigns result, i;
        loop variant length - i;
    */
    for(int i=0; i<length;i++)
        result+=values[i];

    return result;
}

/*@
    ensures \result == (float)(a+b);
*/
float f_add(int a, int b){
    return a+b;
}



/*@
    logic float f_sum_to_index(float* values, integer index) = 
        (index<0)? (float)(0): (float)(values[index]+(float)f_sum_to_index(values, index-1));

    logic float f_sum(float* values, integer length) = (float)(f_sum_to_index(values, length-1));
*/

/*@
    requires valid_array: \valid_read(values+(0..length-1));
    requires valid_length: 0<=length<=50;

    assigns \nothing;

    ensures \result == (float)(f_sum(values, length));
*/
float f_sum(float* values, int length){
    float result = 0.0f;
    /*@
        loop invariant termination_inv: 0<=i<=length;
        loop invariant calculation_inv: result == (float)(f_sum_to_index(values, i-1));
        loop assigns result, i;
        loop variant length-i;
    */
    for(int i=0; i<length; i++)
        result+=values[i];
    return result;
}
