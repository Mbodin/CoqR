{ strrep("ABC", 2) }
{ strrep(c("A", "B", "C"), 1 : 3) }
{ strrep("X", 1 : 5) }
.Internal(strrep(NULL, 5))", "cat("character(0)\n")
.Internal(strrep('aa', NULL))", "cat("character(0)\n")
{ .Internal(strrep(, '') }
{ .Internal(strrep('', ) }
