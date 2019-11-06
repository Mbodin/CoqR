#!/usr/bin/perl
use strict ;
use warnings ;
use autodie ;

my $dir = 'Rlib/base/' ;

opendir (my $DIR, $dir) ;

my $previous = 'Rlib/bootstrapping.state ';

foreach my $file (sort readdir $DIR) {
  next unless ($file =~ /([a-zA-Z0-9_.-]*)\.R$/) ;

  my $base = $dir . $1 ;
  my $r = $base . '.R' ;
  my $state = $base . '.state' ;

  print "$state: $previous src/runR.native\n" ;
  print "\tcat $r | src/runR.native -initial-state \$< -final-state \$@ > /dev/null\n\n" ;

  $previous = $state ;
}

closedir ($DIR) ;

print "Rlib/base.state: $previous\n" ;
print "\tcp -f \$< \$@\n\n" ;

