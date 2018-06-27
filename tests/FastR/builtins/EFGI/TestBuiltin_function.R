eval(call('function', 1, expression(x + 1)[[1]]))
eval(call('function', as.pairlist(list(x=4)), expression(x + 1)[[1]]))
do.call('function', list(as.pairlist(list(x=4)), expression(x + 1)[[1]]))
