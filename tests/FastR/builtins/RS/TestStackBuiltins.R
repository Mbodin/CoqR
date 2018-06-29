parent.frame(-1)
sys.nframe()
sys.call(-2)
sys.calls()
n <- 100; v <- 123; class(v) <- 'cls'; foo <- function(o) { n <- 101; UseMethod('foo') }; foo.cls <- function(o) { n <- 102; NextMethod() }; 
n <- 100; v <- 123; class(v) <- 'cls'; foo <- function(o) { n <- 101; UseMethod('foo') }; foo.cls <- function(o) { n <- 102; NextMethod() };
