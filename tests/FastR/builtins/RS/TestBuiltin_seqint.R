argv <- list(16146, by = 1, length.out = 4);do.call('seq.int', argv);
argv <- list(0.9, 0.95, length.out = 16);do.call('seq.int', argv);
argv <- list(FALSE);seq.int(argv[[1]]);
argv <- list(1.2e+100, 1.3e+100, length.out = 2);do.call('seq.int', argv);
argv <- list(structure(0.88, .Names = 'Other'), structure(1, .Names = 'Vanilla Cream'), length.out = 24);do.call('seq.int', argv);
argv <- list(953553600, by = 86400, length.out = 10);do.call('seq.int', argv);
argv <- list(25L);seq.int(argv[[1]]);
argv <- list(from = 2.0943951023932, to = 2.61799387799149, by = 0.0174532925199433);do.call('seq.int', argv);
argv <- list(from = 0, to = 0.793110173512391, length.out = FALSE);do.call('seq.int', argv);
argv <- list(from = 0, to = structure(-1, .Names = 'c0'));do.call('seq.int', argv);
argv <- list(10L, 99L, 1);do.call('seq.int', argv);
argv <- list(1L);seq.int(argv[[1]]);
argv <- list(102L, 112L, 1L);do.call('seq.int', argv);
argv <- list(from = 0.95, by = -0.120360949612403, length.out = 6);do.call('seq.int', argv);
argv <- list(list());seq.int(argv[[1]]);
argv <- list(-0.2, 1, length.out = 7);do.call('seq.int', argv);
argv <- list(from = 0.070740277703696, to = 0.793110173512391, length.out = NULL);do.call('seq.int', argv);
argv <- list(105L, 112L, 3L);do.call('seq.int', argv);
argv <- list(0, length.out = 3L);do.call('seq.int', argv);
argv <- list(0, structure(345600, tzone = 'GMT'), 43200);do.call('seq.int', argv);
argv <- list(-7, 7, length.out = 11);do.call('seq.int', argv);
argv <- list(4, 4L);do.call('seq.int', argv);
argv <- list(0L, 49, 1);do.call('seq.int', argv);
argv <- list(1, 1, by = 1);do.call('seq.int', argv);
argv <- list(NaN, NaN);do.call('seq.int', argv)
argv <- structure(list(1.2, 1, by = 1), .Names = c('', '', 'by'));do.call('seq.int', argv)
argv <- structure(list(to = NaN), .Names = 'to');do.call('seq.int', argv)
argv <- list(NaN);do.call('seq.int', argv)
{ seq.int.cls <- function(x) 42; seq.int(structure(c(1,2), class='cls')); }
