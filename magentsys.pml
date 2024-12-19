
byte GRID_SIZE = 10;
byte grid[10][10];
byte CHARGING_X 0
byte CHARGING_Y 0
byte FREE 0
byte TARGET 1
byte OBSTACLE 2
byte EXPLORED 3
byte BATTERY_LOW 20
byte BATTERY_FULL 100


byte grid[10][10] = {
    {0,1,0,2,0,0,2,1,0,0},
    {0,2,0,1,0,0,0,2,0,0},
    {0,0,2,0,0,1,0,0,2,0},
    {2,0,1,0,2,0,0,0,0,0},
    {0,0,2,0,1,0,2,0,0,0},
    {0,2,0,0,0,2,0,1,0,0},
    {0,1,0,2,0,0,0,0,2,0},
    {2,0,0,0,2,0,1,0,0,0},
    {0,0,2,1,0,0,0,2,0,0},
    {0,2,0,0,0,2,0,0,0,0}
};


byte pos1_x = 0, pos1_y = 0;       // Agent 1 position
byte pos2_x = 9, pos2_y = 9;       // Agent 2 position
byte battery1 = BATTERY_FULL;
byte battery2 = BATTERY_FULL;


mtype = {IDLE, MOVING, EXPLORING, CHARGING, FAILED};
mtype status1 = IDLE;
mtype status2 = IDLE;


mtype = {WEAK, OK, STRONG};
mtype SNR = STRONG;


bool moving1 = false;
bool moving2 = false;
bool all_explored = false;


inline valid_move(x, y) {
    (x >= 0 && x < GRID_SIZE && 
     y >= 0 && y < GRID_SIZE && 
     grid[x][y] != OBSTACLE)
}

inline at_charging_station(x, y) {
    (x == CHARGING_X && y == CHARGING_Y)
}

inline check_exploration_complete() {
    atomic {
        bool temp = true;
        byte i, j;
        for(i : 0 .. GRID_SIZE-1) {
            for(j : 0 .. GRID_SIZE-1) {
                if
                :: (grid[i][j] == TARGET) -> temp = false
                :: else -> skip
                fi
            }
        }
        all_explored = temp;
    }
}


proctype Agent1() {
    do
    :: atomic {
        if
        :: (status1 == IDLE && battery1 > BATTERY_LOW && SNR != WEAK) ->
            byte next_x = pos1_x;
            byte next_y = pos1_y;
            
            // Try to move
            if
            :: (next_x < GRID_SIZE-1 && valid_move(next_x+1, next_y)) -> 
                next_x++
            :: (next_x > 0 && valid_move(next_x-1, next_y)) -> 
                next_x--
            :: (next_y < GRID_SIZE-1 && valid_move(next_x, next_y+1)) -> 
                next_y++
            :: (next_y > 0 && valid_move(next_x, next_y-1)) -> 
                next_y--
            fi;

            if
            :: (next_x != pos1_x || next_y != pos1_y) ->
                moving1 = true;
                pos1_x = next_x;
                pos1_y = next_y;
                battery1 = battery1 - 1;
                
                // Mark target as explored if found
                if
                :: (grid[pos1_x][pos1_y] == TARGET) ->
                    grid[pos1_x][pos1_y] = EXPLORED;
                    check_exploration_complete()
                :: else -> skip
                fi;
                
                moving1 = false
            :: else -> skip
            fi

        :: (battery1 <= BATTERY_LOW) ->
            status1 = CHARGING;
            if
            :: at_charging_station(pos1_x, pos1_y) ->
                battery1 = BATTERY_FULL;
                status1 = IDLE
            :: else -> skip
            fi

        :: (SNR == WEAK) ->
            status1 = IDLE
        fi
    }
    od
}


proctype Agent2() {
    do
    :: atomic {
        if
        :: (moving1 && status2 == IDLE && battery2 > BATTERY_LOW && SNR != WEAK) ->
            byte next_x = pos2_x;
            byte next_y = pos2_y;
            
            if
            :: (next_x < GRID_SIZE-1 && valid_move(next_x+1, next_y)) -> 
                next_x++
            :: (next_x > 0 && valid_move(next_x-1, next_y)) -> 
                next_x--
            :: (next_y < GRID_SIZE-1 && valid_move(next_x, next_y+1)) -> 
                next_y++
            :: (next_y > 0 && valid_move(next_x, next_y-1)) -> 
                next_y--
            fi;

            if
            :: (next_x != pos2_x || next_y != pos2_y) ->
                moving2 = true;
                pos2_x = next_x;
                pos2_y = next_y;
                battery2 = battery2 - 1;
                
                if
                :: (grid[pos2_x][pos2_y] == TARGET) ->
                    grid[pos2_x][pos2_y] = EXPLORED;
                    check_exploration_complete()
                :: else -> skip
                fi;
                
                moving2 = false
            :: else -> skip
            fi

        :: (battery2 <= BATTERY_LOW) ->
            status2 = CHARGING;
            if
            :: at_charging_station(pos2_x, pos2_y) ->
                battery2 = BATTERY_FULL;
                status2 = IDLE
            :: else -> skip
            fi

        :: (SNR == WEAK) ->
            status2 = IDLE
        fi
    }
    od
}


ltl safety_collision {
    []!(pos1_x == pos2_x && pos1_y == pos2_y)
}

ltl safety_signal {
    [](SNR == WEAK -> 
        ((status1 == IDLE && status2 == IDLE) U SNR != WEAK))
}

ltl liveness_exploration {
    <>all_explored
}

ltl liveness_reactive {
    [](moving1 -> <>moving2)
}

ltl charging_priority {
    []((battery1 <= BATTERY_LOW && battery2 <= BATTERY_LOW) -> 
        (status2 == IDLE U battery1 > BATTERY_LOW))
}


init {
    atomic {
        run Agent1();
        run Agent2();
    }
}


