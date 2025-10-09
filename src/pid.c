#include "pid.h"
#include <float.h>
#include "main.h"

#define SIGN(x) (x>0?1:-1)
#define FLOAT_TOL_ 0.1f

/*@
    predicate float_finite_and_in_range(float val, float low_bound, float up_bound) = 
        \is_finite(val) && (low_bound <= val <= up_bound);
*/

/*@ 
    requires valid_pointer: \valid(pid_con); 
    requires valid_Ts: float_finite_and_in_range(pid_con->Ts, 0.01f, 1.0f);
    requires valid_previous_error: float_finite_and_in_range(previous_error_value, (float)-3300, (float)3300);
    requires valid_error: float_finite_and_in_range(pid_con->error_value, (float)(-3300.0-FLOAT_TOL_), (float)(3300.0f+FLOAT_TOL_));
    requires valid_integrator_ub: float_finite_and_in_range(pid_con->error_integral_ub, 0.0f, (float)(2000.0f*0.5f*3300.0f));
    requires valid_integrator_lb: float_finite_and_in_range(pid_con->error_integral_lb, (float)((-20.0f/0.01)*0.5f*(float)MAX_VOLTAGE), 0.0f);
    requires valid_integrator_error: float_finite_and_in_range(pid_con->error_integral, pid_con->error_integral_lb, pid_con->error_integral_ub);

    assigns pid_con->error_integral;
    ensures (float)pid_con->error_integral_lb <= (float)pid_con->error_integral <= (float)pid_con->error_integral_ub;
    ensures \is_finite(pid_con->error_integral);
*/
void pid_integral_error(pid_controller* pid_con, float previous_error_value){
    float current_integral = pid_con->Ts * ((previous_error_value + pid_con->error_value)/2);
    if(pid_con->error_integral + current_integral > pid_con->error_integral_ub)
        pid_con->error_integral = pid_con->error_integral_ub;
    else if(pid_con->error_integral + current_integral < pid_con->error_integral_lb)
        pid_con->error_integral = pid_con->error_integral_lb;
    else 
        pid_con->error_integral += current_integral;
}



/*@
    requires valid_pointer: \valid(pid_con);
    requires valid_target_value: float_finite_and_in_range(pid_con->target_value, 0.0f, 3300.0f);
    requires valid_controlled_value: float_finite_and_in_range(pid_con->controlled_value, 0.0f, 3300.0f);
    requires valid_error: float_finite_and_in_range(pid_con->error_value, (float)-3300.0, 3300.0f);
    requires valid_kp: float_finite_and_in_range(pid_con->kp, 0.0f, 100.0f);
    requires valid_ki: float_finite_and_in_range(pid_con->ki, 0.0f, 100.0f);
    requires valid_kd: float_finite_and_in_range(pid_con->kd, 0.0f, 100.0f);
    requires valid_Ts: float_finite_and_in_range(pid_con->Ts, 0.01f, 1.0f);
    requires valid_integrator_ub: float_finite_and_in_range(pid_con->error_integral_ub, 0.0f, (float)(2000.0f*0.5f*3300.0f));
    requires valid_integrator_lb: float_finite_and_in_range(pid_con->error_integral_lb, (float)((-20.0f/0.01)*0.5f*(float)MAX_VOLTAGE), 0.0f);
    requires valid_integrator_error: float_finite_and_in_range(pid_con->error_integral, pid_con->error_integral_lb, pid_con->error_integral_ub);
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

    pid_integral_error(pid_con, previous_error_value);
    float integral_contribution = pid_con->ki * pid_con->error_integral;
    // assert \is_finite(pid_con->ki);
    // assert \is_finite(pid_con->error_integral);
    // assert error_integral_range: (float)pid_con->error_integral_lb <= (float)pid_con->error_integral <= (float)pid_con->error_integral_ub;
    // assert integral_gain_range: (float)0.0<=pid_con->ki<=(float)100.0;
    // assert integral_contr_range: (float)(1000.0f * pid_con->error_integral_lb - FLOAT_TOL_)<= integral_contribution <= (float)(1000.0f * pid_con->error_integral_ub + FLOAT_TOL_);

    pid_con->actuator_effort += integral_contribution;
    pid_con->actuator_effort = (pid_con->actuator_effort>pid_con->controller_saturation)?pid_con->controller_saturation:pid_con->actuator_effort;
    
}