#include "pid.h"
#include <float.h>
#include "main.h"

#define SIGN(x) (x>0?1:-1)
#define MAX(x, y) ((x>y)?x:y)
#define FLOAT_TOL_ 0.1f

/*@

    predicate float_finite_and_in_range(float val, float low_bound, float up_bound) = 
        \is_finite(val) && (low_bound <= val <= up_bound);

*/

/*@ 
    logic float integral(float a, float b, float delta_x) = 
        (float)(delta_x * ((a + b)/2));

    logic float bounded_integrator(pid_controller* pid_con, float old_error_integral, float previous_error_value) =
        (old_error_integral + integral(pid_con->error_value, previous_error_value, pid_con->Ts) > pid_con->error_integral_ub) ? pid_con->error_integral_ub :
        (old_error_integral + integral(pid_con->error_value, previous_error_value, pid_con->Ts) < pid_con->error_integral_lb) ? pid_con->error_integral_lb :
        (float)(old_error_integral + integral(pid_con->error_value, previous_error_value, pid_con->Ts));
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

    behavior integrator_ub:
        assumes pid_con->error_integral + integral(pid_con->error_value, previous_error_value, pid_con->Ts) > pid_con->error_integral_ub;
        ensures pid_con->error_integral == pid_con->error_integral_ub;
    behavior integrator_lb:
        assumes pid_con->error_integral + integral(pid_con->error_value, previous_error_value, pid_con->Ts) < pid_con->error_integral_lb;
        ensures pid_con->error_integral == pid_con->error_integral_lb;
    behavior integrator_ok:
        assumes pid_con->error_integral + integral(pid_con->error_value, previous_error_value, pid_con->Ts) <= pid_con->error_integral_ub &&
                pid_con->error_integral + integral(pid_con->error_value, previous_error_value, pid_con->Ts) >= pid_con->error_integral_lb;
        ensures pid_con->error_integral == \old(pid_con->error_integral) + integral(pid_con->error_value, previous_error_value, pid_con->Ts);
    complete behaviors;
    disjoint behaviors;

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
    requires valid_saturation_value: float_finite_and_in_range(pid_con->controller_saturation, 0.0f, 3300.0f);
    requires valid_error: float_finite_and_in_range(pid_con->error_value, (float)-3300.0, 3300.0f);
    requires valid_kp: float_finite_and_in_range(pid_con->kp, 0.0f, 100.0f);
    requires valid_ki: float_finite_and_in_range(pid_con->ki, 0.0f, 100.0f);
    requires valid_kd: float_finite_and_in_range(pid_con->kd, 0.0f, 100.0f);
    requires valid_Ts: float_finite_and_in_range(pid_con->Ts, 0.01f, 1.0f);
    requires valid_integrator_ub: float_finite_and_in_range(pid_con->error_integral_ub, 0.0f, (float)(2000.0f*0.5f*3300.0f));
    requires valid_integrator_lb: float_finite_and_in_range(pid_con->error_integral_lb, (float)((-20.0f/0.01)*0.5f*(float)MAX_VOLTAGE), 0.0f);
    requires valid_integrator_error: float_finite_and_in_range(pid_con->error_integral, pid_con->error_integral_lb, pid_con->error_integral_ub);

    assigns pid_con->actuator_effort;
    assigns pid_con->error_value;
    assigns pid_con->error_integral;

    ensures pid_con->error_value == pid_con->target_value - pid_con->controlled_value;
    ensures pid_con->error_integral == bounded_integrator(pid_con, \old(pid_con->error_integral), \old(pid_con->error_value));
    ensures 0.0f<=pid_con->actuator_effort <= pid_con->controller_saturation;
    ensures \let e = (pid_con->target_value - pid_con->controlled_value);
            \let p = pid_con->kp * e;
            \let d = pid_con->kd * ((e - \old(pid_con->error_value)) / pid_con->Ts);
            \let i = pid_con->ki * bounded_integrator(pid_con, \old(pid_con->error_integral), \old(pid_con->error_value));
            \let effort = (float)(p + i + d);
            (pid_con->actuator_effort == ((effort >= pid_con->controller_saturation) ? pid_con->controller_saturation : 
                                         ((effort < 0.0f) ? 0.0f : effort)));



*/
void pid_compute_actuator_command(pid_controller* pid_con){
    float previous_error_value = pid_con->error_value;
    pid_con->error_value = pid_con->target_value - pid_con->controlled_value;
    //@ ghost float error_value_range_ub = 3300.0f+FLOAT_TOL_;
    //@ ghost float error_value_range_lb = -3300.0f-FLOAT_TOL_;
    //@ assert error_value_range: error_value_range_lb <=pid_con->error_value<=error_value_range_ub;

    float proportional_contribution = pid_con->kp * pid_con->error_value;
    pid_con->actuator_effort = proportional_contribution;
    //@ ghost float prop_contr_ub = (3300.0f+FLOAT_TOL_)*100.0f;
    //@ ghost float prop_contr_lb = (-3300.0-FLOAT_TOL_)*100.0f;
    //@ assert prop_contr_range: prop_contr_lb<=proportional_contribution<=prop_contr_ub;
    //@ assert prop_contr_act_eff_range: prop_contr_lb<=pid_con->actuator_effort<=prop_contr_ub;

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
    //@ ghost float deriv_contr_ub = (660000.0f+2*FLOAT_TOL_)*100.0f;
    //@ ghost float deriv_contr_lb = (-660000.0f-2*FLOAT_TOL_)*100.0f;
    //@ assert deriv_contr_range: deriv_contr_lb<=derivative_contribution<=deriv_contr_ub;
    pid_con->actuator_effort += derivative_contribution;
    //@ assert deriv_contr_act_eff_range: deriv_contr_lb+prop_contr_lb<=pid_con->actuator_effort<=deriv_contr_ub+prop_contr_ub;

    pid_integral_error(pid_con, previous_error_value);
    float integral_contribution = pid_con->ki * pid_con->error_integral;
    // assert \is_finite(pid_con->ki);
    // assert \is_finite(pid_con->error_integral);
    // assert integral_gain_range: (float)0.0<=pid_con->ki<=(float)100.0;

    //@ ghost float integ_contr_ub = 100.0f * pid_con->error_integral_ub;
    //@ ghost float integ_contr_lb = 100.0f * pid_con->error_integral_lb;
    //@ assert error_integral_range: (float)pid_con->error_integral_lb <= (float)pid_con->error_integral <= (float)pid_con->error_integral_ub;
    //@ assert integral_contr_range: integ_contr_lb<= integral_contribution <= integ_contr_ub;
    //@ assert \is_finite(pid_con->actuator_effort);
    //@ assert \is_finite(integral_contribution);

    //@ assert deriv_contr_lb+prop_contr_lb<=pid_con->actuator_effort<=deriv_contr_ub+prop_contr_ub;
    //@ assert deriv_contr_lb+prop_contr_lb+integ_contr_lb <= pid_con->actuator_effort + integral_contribution<=deriv_contr_ub+prop_contr_ub+integ_contr_ub;
    //@ assert -1e10f <= pid_con->actuator_effort <= 1e10f;
    //@ assert -1e10f <= integral_contribution <= 1e10f;
    float total_actuator_effort = pid_con->actuator_effort + integral_contribution;
    //@ assert deriv_plus_int_contr_act_eff_range: (float)(deriv_contr_lb+prop_contr_lb+integ_contr_lb) <=total_actuator_effort<=(float)(deriv_contr_ub+prop_contr_ub+integ_contr_ub);

    pid_con->actuator_effort = total_actuator_effort;

    // pid_con->actuator_effort = (pid_con->actuator_effort>=pid_con->controller_saturation)?
                                    // pid_con->controller_saturation:MAX(pid_con->actuator_effort, 0.0f);
    if (pid_con->actuator_effort >= pid_con->controller_saturation) {
        pid_con->actuator_effort = pid_con->controller_saturation;
        //@ assert  pid_con->actuator_effort == pid_con->controller_saturation;
        //@ assert 0.0f <= pid_con->actuator_effort <= pid_con->controller_saturation;
    } else if (pid_con->actuator_effort < 0.0f) {
        pid_con->actuator_effort = 0.0f;
        //@ assert  pid_con->actuator_effort == 0;
        //@ assert 0.0f <= pid_con->actuator_effort <= pid_con->controller_saturation;
    } else {
        pid_con->actuator_effort = pid_con->actuator_effort;
        //@ assert 0.0f <= pid_con->actuator_effort <= pid_con->controller_saturation;
    }
    //@ assert 0.0f <= pid_con->actuator_effort <= pid_con->controller_saturation;
}