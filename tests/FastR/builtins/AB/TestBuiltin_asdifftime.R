argv <- structure(list(tim = c('0:3:20', '11:23:15')), .Names = 'tim');do.call('as.difftime', argv)
argv <- structure(list(tim = c('3:20', '23:15', '2:'), format = '%H:%M'),     .Names = c('tim', 'format'));do.call('as.difftime', argv)
