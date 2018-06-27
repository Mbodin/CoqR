argv <- list(1L, '%s is not TRUE', '%s are not all TRUE', NULL); .Internal(ngettext(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
argv <- list(2L, '%s is not TRUE', '%s are not all TRUE', NULL); .Internal(ngettext(argv[[1]], argv[[2]], argv[[3]], argv[[4]]))
{ ngettext(1, "a", "b") }
{ ngettext(0, "a", "b") }
{ ngettext(42, "a", "b") }
{ ngettext(1, c("a"), "b") }
{ ngettext(1, "a", c("b")) }
{ ngettext(c(1), "a", "b") }
{ ngettext(c(1,2), "a", "b") }
{ ngettext(1+1i, "a", "b") }
{ ngettext(1, NULL, "b") }
{ ngettext(1, "a", NULL) }
{ ngettext(1, NULL, NULL) }
{ ngettext(1, c("a", "c"), "b") }
{ ngettext(1, "a", c("b", "c")) }
{ ngettext(1, c(1), "b") }
{ ngettext(1, "a", c(1)) }
{ ngettext(-1, "a", "b") }
