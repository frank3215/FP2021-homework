-- init x = take ((length x)-1) x

init x = reverse(tail(reverse(x)))
