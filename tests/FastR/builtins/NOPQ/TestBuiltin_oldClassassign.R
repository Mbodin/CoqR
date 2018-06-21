argv <- list(list(), NULL);`oldClass<-`(argv[[1]],argv[[2]]);
argv <- list(NULL, NULL);`oldClass<-`(argv[[1]],argv[[2]]);
{ x<-1; oldClass(x)<-"foo"; class(x) }
{ x<-1; oldClass(x)<-"foo"; oldClass(x) }
{ x<-1; oldClass(x)<-"integer"; class(x) }
{ x<-1; oldClass(x)<-"integer"; oldClass(x) }
{ x<-1; oldClass(x)<-"integer"; class(x)<-"integer"; class(x) }
{ x<-1; oldClass(x)<-"integer"; class(x)<-"integer"; oldClass(x) }
