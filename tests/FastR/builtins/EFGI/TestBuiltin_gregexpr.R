argv <- list('', 'abc', FALSE, FALSE, FALSE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('[^.w:?$@[]]+', 'version$m', FALSE, TRUE, FALSE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('$', 'version$m', FALSE, FALSE, TRUE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('éè', '«Latin-1 accented chars»: éè øØ å<Å æ<Æ é éè', FALSE, FALSE, TRUE, TRUE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('', 'abc', FALSE, TRUE, FALSE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('', 'abc', FALSE, FALSE, TRUE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('éè', '«Latin-1 accented chars»: éè øØ å<Å æ<Æ é éè', TRUE, FALSE, FALSE, TRUE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('[[:space:]]?(,|,?[[:space:]]and)[[:space:]]+', character(0), FALSE, FALSE, FALSE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('[[^]]*]', 'FALSE', FALSE, FALSE, FALSE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('(?<first>[[:upper:]][[:lower:]]+) (?<last>[[:upper:]][[:lower:]]+)', c('  Ben Franklin and Jefferson Davis', 'tMillard Fillmore'), FALSE, TRUE, FALSE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('?', 'utils::data', FALSE, FALSE, TRUE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- list('[[', 'utils:::.show_help_on_topic_', FALSE, FALSE, TRUE, FALSE); .Internal(gregexpr(argv[[1]], argv[[2]], argv[[3]], argv[[4]], argv[[5]], argv[[6]]))
argv <- structure(list(pattern = '', text = 'abc', fixed = TRUE),     .Names = c('pattern', 'text', 'fixed'));do.call('gregexpr', argv)
argv <- structure(list(pattern = '', text = 'abc'), .Names = c('pattern',     'text'));do.call('gregexpr', argv)
argv <- structure(list(pattern = '', text = 'abc', perl = TRUE),     .Names = c('pattern', 'text', 'perl'));do.call('gregexpr', argv)
gregexpr("e",c("arm","foot","lefroo", "bafoobar"))
gregexpr("(a)[^a]1", c("andrea apart", "amadeus", NA))
{ x<-gregexpr("foo", c("bar foo foo", "foo"), fixed=T); as.integer(c(x[[1]], x[[2]])) }
{ x<-gregexpr("foo", c("bar foo foo", "foo"), fixed=F); as.integer(c(x[[1]], x[[2]])) }
{ x<-gregexpr("foo", c("bar foo foo", "foo"), fixed=T); list(attr(x[[1]], "match.length"), attr(x[[2]], "match.length")) }
{ x<-gregexpr("foo", c("bar foo foo", "foo"), fixed=F); list(attr(x[[1]], "match.length"), attr(x[[2]], "match.length")) }
{ .Internal(gregexpr(7, "42", F, F, F, F)) }
{ .Internal(gregexpr(character(), "42", F, F, F, F)) }
{ .Internal(gregexpr("7", 42, F, F, F, F)) }
{ argv <- structure(list(pattern = '', text = c('abc', 'defg'), perl = TRUE),     .Names = c('pattern', 'text', 'perl'));do.call('gregexpr', argv) }
{ x<-c("Aaa Bbb Aaa bbb", "Aaa Bbb Aaa Bbb", "Aaa bbb Aaa bbb"); p<-"(?<first>[[:upper:]][[:lower:]]+) (?<last>[[:upper:]][[:lower:]]+)"; gregexpr(p, x, perl=TRUE) }
{ x<-c("Aaa bbb Aaa bbb", "Aaa Bbb Aaa Bbb", "Aaa Bbb Aaa bbb"); p<-"(?<first>[[:upper:]][[:lower:]]+) (?<last>[[:upper:]][[:lower:]]+)"; gregexpr(p, x, perl=TRUE) }
{ x<-c("Aaa bbb Aaa Bbb", "Aaa bbb Aaa bbb", "Aaa bbb Aaa Bbb"); p<-"(?<first>[[:upper:]][[:lower:]]+) (?<last>[[:upper:]][[:lower:]]+)"; gregexpr(p, x, perl=TRUE) }
{ x<-c("Aaa bbb Aaa bbb", "Aaa Bbb Aaa Bbb", "Aaa bbb Aaa bbb"); p<-"(?<first>[[:upper:]][[:lower:]]+) (?<last>[[:upper:]][[:lower:]]+)"; gregexpr(p, x, perl=TRUE) }
gregexpr(')', 'abc()', fixed = TRUE)
gregexpr('(', 'abc()', fixed = TRUE)
gregexpr(')', 'abc()', fixed = FALSE)
gregexpr(')', 'abc()', fixed = FALSE)
gregexpr('(', 'abc()', fixed = FALSE)
gregexpr('(', 'abc()', fixed = FALSE)
