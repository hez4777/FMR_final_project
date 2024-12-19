/* Constants */
#define N 10
#define BATT_FULL 100
#define BATT_LOW 20

/* State space */
byte grid[100];  /* Single dimensional array for N*N grid */
#define GRID(x,y) grid[(x)*N + (y)]

byte pos1_x;
byte pos1_y;
byte pos2_x;
byte pos2_y;
byte battery1;
byte battery2;
byte status1;
byte status2;
byte snr;
bool moving1;
bool moving2;
bool all_explored;

/* Agent 1 (Leader) Process */
proctype Agent1() {
    byte next_x;
    byte next_y;
    
    do
    :: atomic {
        if
        :: (status1 == 0 && battery1 > BATT_LOW) -> 
            next_x = pos1_x;
            next_y = pos1_y;
            
            /* Movement selection */
            if
            :: (next_x < (N-1)) && (GRID(next_x+1, next_y) != 2) -> 
                next_x = next_x + 1
            :: (next_x > 0) && (GRID(next_x-1, next_y) != 2) -> 
                next_x = next_x - 1
            :: (next_y < (N-1)) && (GRID(next_x, next_y+1) != 2) -> 
                next_y = next_y + 1
            :: (next_y > 0) && (GRID(next_x, next_y-1) != 2) -> 
                next_y = next_y - 1
            :: else -> skip
            fi;
            
            /* Execute movement */
            if
            :: (next_x != pos1_x || next_y != pos1_y) ->
                moving1 = true;
                pos1_x = next_x;
                pos1_y = next_y;
                battery1 = battery1 - 1;
                
                if
                :: (GRID(pos1_x, pos1_y) == 1) ->
                    GRID(pos1_x, pos1_y) = 3;
                    all_explored = false
                :: else -> skip
                fi;
                
                moving1 = false
            :: else -> skip
            fi

        :: (battery1 <= BATT_LOW) ->
            status1 = 3;  /* CHARGING */
            if
            :: (pos1_x == 0 && pos1_y == 0) ->
                battery1 = BATT_FULL;
                status1 = 0  /* IDLE */
            :: else -> skip
            fi

        :: (snr == 0) ->  /* WEAK signal */
            status1 = 0    /* IDLE */
        fi
    }
    od
}

/* Agent 2 (Follower) Process */
proctype Agent2() {
    byte next_x;
    byte next_y;
    
    do
    :: atomic {
        if
        :: (moving1 && status2 == 0 && battery2 > BATT_LOW && snr != 0) ->
            next_x = pos2_x;
            next_y = pos2_y;
            
            /* Movement selection */
            if
            :: (next_x < (N-1)) && (GRID(next_x+1, next_y) != 2) -> 
                next_x = next_x + 1
            :: (next_x > 0) && (GRID(next_x-1, next_y) != 2) -> 
                next_x = next_x - 1
            :: (next_y < (N-1)) && (GRID(next_x, next_y+1) != 2) -> 
                next_y = next_y + 1
            :: (next_y > 0) && (GRID(next_x, next_y-1) != 2) -> 
                next_y = next_y - 1
            :: else -> skip
            fi;

            /* Execute movement */
            if
            :: (next_x != pos2_x || next_y != pos2_y) ->
                moving2 = true;
                pos2_x = next_x;
                pos2_y = next_y;
                battery2 = battery2 - 1;
                
                if
                :: (GRID(pos2_x, pos2_y) == 1) ->
                    GRID(pos2_x, pos2_y) = 3;
                    all_explored = false
                :: else -> skip
                fi;
                
                moving2 = false
            :: else -> skip
            fi

        :: (battery2 <= BATT_LOW) ->
            status2 = 3;  /* CHARGING */
            if
            :: (pos2_x == 0 && pos2_y == 0) ->
                battery2 = BATT_FULL;
                status2 = 0  /* IDLE */
            :: else -> skip
            fi

        :: (snr == 0) ->  /* WEAK signal */
            status2 = 0    /* IDLE */
        fi
    }
    od
}

/* Initialization */
init {
    atomic {
        /* Initialize grid with targets and obstacles */
        GRID(0,1) = 1; GRID(0,3) = 2; GRID(0,6) = 2; GRID(0,7) = 1;
        GRID(1,1) = 2; GRID(1,3) = 1; GRID(1,7) = 2;
        GRID(2,2) = 2; GRID(2,5) = 1; GRID(2,8) = 2;
        GRID(3,0) = 2; GRID(3,2) = 1; GRID(3,4) = 2;
        GRID(4,2) = 2; GRID(4,4) = 1; GRID(4,6) = 2;
        GRID(5,1) = 2; GRID(5,5) = 2; GRID(5,7) = 1;
        GRID(6,1) = 1; GRID(6,3) = 2; GRID(6,8) = 2;
        GRID(7,0) = 2; GRID(7,4) = 2; GRID(7,6) = 1;
        GRID(8,2) = 2; GRID(8,3) = 1; GRID(8,7) = 2;
        GRID(9,1) = 2; GRID(9,5) = 2;
        
        /* Initialize agents */
        pos1_x = 0; pos1_y = 0;
        pos2_x = N-1; pos2_y = N-1;
        battery1 = BATT_FULL;
        battery2 = BATT_FULL;
        status1 = 0;
        status2 = 0;
        snr = 2;
        moving1 = false;
        moving2 = false;
        all_explored = false;
        
        run Agent1();
        run Agent2();
    }
}

/* LTL Properties */


ltl liveness_exploration {
    <>all_explored
}

ltl liveness_reactive {
    [](moving1 -> <>moving2)
}

ltl safety_collision {
    []!(pos1_x == pos2_x && pos1_y == pos2_y)
}

ltl safety_signal {
    [](snr == 0 -> ((status1 == 0 && status2 == 0) U snr != 0))
}

ltl charging_priority {
    []((battery1 <= BATT_LOW && battery2 <= BATT_LOW) -> 
       (status2 == 0 U battery1 > BATT_LOW))
}



