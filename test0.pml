int x = 0;

proctype Incrementer() {
    do
    :: x = x + 1; printf("Incremented x: %d\n", x)
    od
}

proctype Decrementer() {
    do
    :: x = x - 1; printf("Decremented x: %d\n", x)
    od
}

init {
    atomic {
        run Incrementer();
        run Decrementer();
    }
}
