argv <- structure(list(text = c('NA', NA, 'BANANA'), first = 1,     last = 1), .Names = c('text', 'first', 'last'));do.call('substring', argv)
argv <- structure(list(text = 'abcdef', first = 1:6, last = 1:6),     .Names = c('text', 'first', 'last'));do.call('substring', argv)
{ substring("123456", first=2, last=4) }
{ substring("123456", first=2.8, last=4) }
{ substring(c("hello", "bye"), first=c(1,2,3), last=4) }
{ substring("fastr", first=NA, last=2) }
