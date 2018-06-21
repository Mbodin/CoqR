{ foo <- function(x) lapply(sys.frames(), function(x) ls(x));boo <- function(bo) bar(bo);callboo <- function(cb) do.call('boo', list(cb));fun <- function(f) callboo(f);fun(42);}

{ foo <- function(x) list(a = ls(sys.frames()[[1]]), b=ls(sys.frames()[[2]]), len=length(sys.frames()));boo <- function(bo) bar(bo);callboo <- function(cb) do.call('boo', list(cb));fun <- function(f) callboo(f);fun(42);}
