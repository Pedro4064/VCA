#include "pid.h"

#define SIGN(x) (x>0?1:-1)

char pid_integral_windup_check(pid_controller* pid_con){
    char is_actuator_sat = (pid_con->actuator_effort == pid_con->controller_saturation);
    char is_controller_counteracting = (SIGN(pid_con->actuator_effort) != SIGN(pid_con->error_value));

    return (is_actuator_sat && !is_controller_counteracting);
}


void pid_compute_actuator_command(pid_controller* pid_con){
    int previous_error_value = pid_con->error_value;
    pid_con->error_value = pid_con->target_value - pid_con->controlled_value;

    pid_con->actuator_effort = pid_con->kp * pid_con->error_value;
    pid_con->actuator_effort += pid_con->kd * ((pid_con->error_value - previous_error_value)/pid_con->Ts);
    if(!pid_integral_windup_check(pid_con)){
        pid_con->error_integral += pid_con->Ts * ((previous_error_value + pid_con->error_value)/2);
        pid_con->actuator_effort += pid_con->ki * pid_con->error_integral;
    }
    
}