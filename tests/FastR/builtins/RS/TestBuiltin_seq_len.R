argv <- list(FALSE);do.call('seq_len', argv);
argv <- list(structure(3.14159265358979, class = structure('3.14159265358979', class = 'testit')));do.call('seq_len', argv);
argv <- list(structure(2, .Names = 'Ind'));do.call('seq_len', argv);
argv <- list(c(2L, 2L));do.call('seq_len', argv)
{ seq_len(10) }
{ seq_len(5L) }
{ seq_len(1:2) }
{ seq_len(integer()) }
{ seq_len(NA) }
{ seq_len(-1) }
{ seq_len(NULL) }
{ seq_len("foo") }
{ seq_len(0) + 1.1; }
