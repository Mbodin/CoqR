argv <- structure(list(year = 1970, month = 1, day = 1, hour = 0,     min = 0, sec = 0, tz = 'GMT'), .Names = c('year', 'month',     'day', 'hour', 'min', 'sec', 'tz'));do.call('ISOdatetime', argv)

argv <- structure(list(year = 2002, month = 6, day = 24, hour = 0,     min = 0, sec = 10), .Names = c('year', 'month', 'day', 'hour',     'min', 'sec'));do.call('ISOdatetime', argv)

