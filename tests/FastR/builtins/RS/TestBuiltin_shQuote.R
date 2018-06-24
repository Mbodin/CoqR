argv <- structure(list(string = c('ABC', '\'123\'', 'a\'b'), type = 'cmd'),     .Names = c('string', 'type'));do.call('shQuote', argv)
