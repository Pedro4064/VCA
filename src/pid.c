#include "pid.h"
#include <float.h>

#define SIGN(x) (x>0?1:-1)
#define FLOAT_TOL_ 0.1f

/*@ 
    requires valid_pointer: \valid(pid_con); 
    assigns \nothing;
*/
char pid_integral_windup_check(pid_controller* pid_con){
    char is_actuator_sat = (pid_con->actuator_effort >= pid_con->controller_saturation);
    char is_controller_counteracting = (SIGN(pid_con->actuator_effort) != SIGN(pid_con->error_value));

    return (is_actuator_sat && !is_controller_counteracting);
}

/*@
    predicate float_finite_and_in_range(float val, float low_bound, float up_bound) = 
        \is_finite(val) && (low_bound <= val <= up_bound);
*/

/*@
    requires valid_pointer: \valid(pid_con);
    requires valid_target_value: float_finite_and_in_range(pid_con->target_value, 0.0f, 3300.0f);
    requires valid_controlled_value: float_finite_and_in_range(pid_con->controlled_value, 0.0f, 3300.0f);
    requires valid_error: float_finite_and_in_range(pid_con->error_value, (float)-3300.0, 3300.0f);
    requires valid_kp: float_finite_and_in_range(pid_con->kp, 0.0f, 100.0f);
    requires valid_ki: float_finite_and_in_range(pid_con->ki, 0.0f, 100.0f);
    requires valid_kd: float_finite_and_in_range(pid_con->kd, 0.0f, 100.0f);
    requires valid_Ts: float_finite_and_in_range(pid_con->Ts, 0.01f, 1.0f);
*/
void pid_compute_actuator_command(pid_controller* pid_con){
    float previous_error_value = pid_con->error_value;
    pid_con->error_value = pid_con->target_value - pid_con->controlled_value;
    //@ assert error_value_range: (float)(-3300.0-FLOAT_TOL_)<=pid_con->error_value<=(3300.0f+FLOAT_TOL_);

    float proportional_contribution = pid_con->kp * pid_con->error_value;
    pid_con->actuator_effort = proportional_contribution;
    //@ assert proportional_contribution_range: (float)((-3300.0-FLOAT_TOL_)*100.0)<=proportional_contribution<=(float)((3300.0f+FLOAT_TOL_)*100.0);

    /* 
        The range for error_value is (-3300,3300), and therefore previous_error-value
       as well. Therefore error_diff = (-6600,6600)
    */
    float error_diff = pid_con->error_value - previous_error_value;
    //@ assert error_diff_range: (float)(-6600-FLOAT_TOL_)<=error_diff<=(float)(6600+FLOAT_TOL_);

    /*
        Considering now that the minimum Ts value (which in turn generates the largest
       error_derivative value) is 0.01 we have the following:
    */
    float error_derivative = (error_diff)/pid_con->Ts;
    //@ assert error_derivative_range: (float)(-660000-FLOAT_TOL_)<=error_derivative<=(float)(660000+FLOAT_TOL_);
    float derivative_contribution = pid_con->kd * (error_derivative);
    //@ assert derivative_gain_range: (float)0.0<=pid_con->kd<=(float)100.0;
    //@ assert derivative_contr_range: (float)((-660000.0-2*FLOAT_TOL_)*100.0)<=derivative_contribution<=(float)((660000.0+2*FLOAT_TOL_)*100.0);

    pid_con->actuator_effort += derivative_contribution;

    if(!pid_integral_windup_check(pid_con)){
        pid_con->error_integral += pid_con->Ts * ((previous_error_value + pid_con->error_value)/2);
        pid_con->actuator_effort += pid_con->ki * pid_con->error_integral;
    }

    pid_con->actuator_effort = (pid_con->actuator_effort>pid_con->controller_saturation)?pid_con->controller_saturation:pid_con->actuator_effort;
    
}