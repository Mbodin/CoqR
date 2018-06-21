parse(text=deparse(c(1, 2, 3)))
{ parse(text=c("for (i in 1:10) {", "    x[i] <- i", "}")) }
eval(parse(text=deparse(data.frame(x=c(1)))))
{ typeof(parse(text = "foo", keep.source = FALSE, srcfile = NULL)[[1]]) }
{ parse(text="NULL") }
parse(text='is.null')
attributes(parse(text='is.null'))
parse(text='somethingthatdoesnotexist')
attributes(parse(text='somethingthatdoesnotexist'))
.Internal(parse(stdin(), c(1,2), c('expr1', 'expr2'), '?', '<weird-text', 'unknown'))
parse(text='', srcfile=srcfile(system.file('testfile')))
p <- parse(text = 'x = 1', keep.source = TRUE); attr(p, 'srcfile')$parseData
structure(c(1L, 3L, 1L, 3L, 1L, 267L, 1L, 5L, 1L, 1L, 1L, 1L, 1L, 263L, 2L, 5L, 1L, 5L, 1L, 5L, 1L, 261L, 3L, 4L, 1L, 5L, 1L, 5L, 0L, 77L, 4L, 5L, 1L, 1L, 1L, 5L, 0L, 77L, 5L, 0L), tokens = c("EQ_ASSIGN", "SYMBOL", "NUM_CONST", "expr", "expr"), text = c("=", "x", "1", "", ""), class = "parseData", .Dim = c(8L, 5L))
p <- parse(text = 'x = x + 1; rnorm(1, std = z); f2 <- function(a=1) a', keep.source = TRUE); attr(p, 'srcfile')$parseData
structure(c(1L, 3L, 1L, 3L, 1L, 267L, 1L, 8L, 1L, 1L, 1L, 1L, 1L, 263L, 2L, 8L, 1L, 5L, 1L, 5L, 1L, 263L, 3L, 7L, 1L, 7L, 1L, 7L, 1L, 43L, 4L, 7L, 1L, 9L, 1L, 9L, 1L, 261L, 5L, 6L, 1L, 9L, 1L, 9L, 0L, 77L, 6L, 7L, 1L, 5L, 1L, 9L, 0L, 77L, 7L, 8L, 1L, 1L, 1L, 9L, 0L, 77L, 8L, 0L, 1L, 12L, 1L, 16L, 1L, 296L, 9L, 13L, 1L, 18L, 1L, 18L, 1L, 261L, 10L, 11L, 1L, 18L, 1L, 18L, 0L, 77L, 11L, 13L, 1L, 27L, 1L, 27L, 1L, 263L, 12L, 13L, 1L, 12L, 1L, 28L, 0L, 77L, 13L, 0L, 1L, 34L, 1L, 35L, 1L, 266L, 14L, 20L, 1L, 31L, 1L, 32L, 1L, 263L, 15L, 20L, 1L, 48L, 1L, 48L, 1L, 261L, 16L, 17L, 1L, 48L, 1L, 48L, 0L, 77L, 17L, 19L, 1L, 51L, 1L, 51L, 1L, 263L, 18L, 19L, 1L, 37L, 1L, 51L, 1L, 264L, 19L, 20L, 1L, 31L, 1L, 51L, 0L, 77L, 20L, 0L), tokens = c("EQ_ASSIGN", "SYMBOL", "SYMBOL", "'+'", "NUM_CONST", "expr", "expr", "expr", "SYMBOL_FUNCTION_CALL", "NUM_CONST", "expr", "SYMBOL", "expr", "LEFT_ASSIGN", "SYMBOL", "NUM_CONST", "expr", "SYMBOL", "FUNCTION", "expr"), text = c("=", "x", "x", "+", "1", "", "", "", "rnorm", "1", "", "z", "", "<-", "f2", "1", "", "a", "function", ""), class = "parseData", .Dim = c(8L, 20L))
