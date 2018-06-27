argv <- list(1L, 1L); .Internal(tabulate(argv[[1]], argv[[2]]))
argv <- list(1:6, 6L); .Internal(tabulate(argv[[1]], argv[[2]]))
argv <- list(integer(0), 1L); .Internal(tabulate(argv[[1]], argv[[2]]))
argv <- list(c(1L, 9L, 13L, 25L, 11L, 24L, 3L, 20L, 20L, 15L, 20L, 14L, 24L, 19L, 12L, 8L, 1L, 11L, 4L, 3L, 21L, 25L, 10L, 3L, 12L), 25L); .Internal(tabulate(argv[[1]], argv[[2]]))
argv <- list(structure(1:49, .Label = c('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '10', '11', '12', '13', '14', '15', '16', '17', '18', '19', '20', '21', '22', '23', '24', '25', '26', '27', '28', '29', '30', '31', '32', '33', '34', '35', '36', '37', '38', '39', '40', '41', '42', '43', '44', '45', '46', '47', '48'), class = 'factor'), 49L); .Internal(tabulate(argv[[1]], argv[[2]]))
argv <- list(integer(0), 0L); .Internal(tabulate(argv[[1]], argv[[2]]))
argv <- structure(list(bin = numeric(0)), .Names = 'bin');do.call('tabulate', argv)
{tabulate(c(2,3,5))}
{tabulate(c(2,3,3,5), nbins = 10)}
{tabulate(c(-2,0,2,3,3,5))}
{tabulate(c(-2,0,2,3,3,5), nbins = 3)}
{tabulate(factor(letters[1:10]))}
{ .Internal(tabulate(c(2,3,5), 7)) }
{ .Internal(tabulate(c(2L,3L,5L), c(7, 42))) }
{ .Internal(tabulate(c(2L,3L,5L), integer())) }
{ .Internal(tabulate(c(2L,3L,5L), -1)) }
{ .Internal(tabulate(c(2L,3L,5L), NA)) }
