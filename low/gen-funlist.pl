#!/usr/bin/perl
use strict ;
use warnings ;

my $true = 1 ;
my $false = 0 ;

my $coqFile = "low/funlist.v" ;

my $mlFile = "low/funlist.ml" ;

my $extractedFile = "low/low.mli" ;


my $fileExist = $false ;

$fileExist = $true if -f $coqFile ;

print "Generating Coq file…\n" ;

if ($fileExist) {
    print "Coq file already there, using it as-is.\n"
} else {
    open (my $outStream, '>', $coqFile) or die "Could not create file $coqFile for some reason." ;
    print $outStream "(* This file has been automatically generated. *)\n" ;
    print $outStream "Require Import Rinit.\n" ;
    print $outStream "SearchAbout result.\n" ;
    close $outStream ;
}

print "Executing Coq file…\n" ;

open (PIPE, "cat low/funlist.v |"
    . "coqtop -R ./lib Lib -R ./lib/tlc/src TLC -R ./low Low -noglob -quiet |")
    or die "Can’t execute Coq for some reason." ;

print "Generating ML file from output…\n" ;

unlink $mlFile if -f $mlFile ;

open (my $mlStream, '>', $mlFile) or die "Could not create file $mlFile for some reason." ;
print $mlStream "(* This file has been automatically generated. *)\n" ;
print $mlStream "(* This file is meant to be rewritten at each compilation: save your changes elsewhere if you really want to edit it. *)\n" ;
print $mlStream "open Low\n" ;
print $mlStream "open Debug\n" ;
print $mlStream "let funlist =\n" ;

my $acc = "" ;

sub check {
    my ($name) = @_ ;
    # This function checks whether a given function has been extracted into OCaml by Coq.
    open (FILE, $extractedFile) or die "Unable to open file $extractedFile for some reason." ;
    while (<FILE>){
        if (/^val $name :/) {
            close FILE ;
            return $true ;
        }
    }
    close FILE ;
    return $false ;
}

while (my $row = <PIPE>){
    $row =~ s/\n$// ;
    if ($row =~ /^[a-zA-Z0-9_]*:/) {
        # We got a full specification in $acc. Let us inspect it.
        if ($acc =~ /^([a-zA-Z0-9_]*):/) {
            my $funName = $1 ;
            $acc =~ s/^([a-zA-Z0-9_]*):// ;
            $acc =~ s/ +/ /g ;

            my $useGlobals = $false ;
            if ($acc =~ /^ Globals ->/){
                $useGlobals = $true ;
                $acc =~ s/^ Globals ->// ;
            }

            my $useRuns = $false ;
            if ($acc =~ /^ runs_type ->/){
                $useRuns = $true ;
                $acc =~ s/^ runs_type ->// ;
            }

            my $endFunction = "(fun " ;
            if ($useGlobals) { $endFunction .= "g " ; } else { $endFunction .= "_ " ; }
            if ($useRuns) { $endFunction .= "r " ; } else { $endFunction .= "_ " ; }
            $endFunction .= "s " ;
            $endFunction .= $funName ;
            if ($useGlobals) { $endFunction .= " g" ; }
            if ($useRuns) { $endFunction .= " r" ; }
            $endFunction .= " s)" ;

            if ($acc =~ / state ->( (nat|int|unit|SExpRec_pointer) ->)* result (nat|int|unit|SExpRec_pointer)/){
                # This function is of interest for us.
                $acc =~ s/ state ->// ;

                # Checking that it has indeed been extracted.
                if (check ($funName)) {
                    $acc =~ /result (nat|int|unit|SExpRec_pointer)$/ ;
                    my $endType = $1 ;
                    $acc =~ s/result .*//g ;

                    if ($endType eq "nat") { $endFunction = "Result_int " . $endFunction ; }
                    elsif ($endType eq "int") { $endFunction = "Result_float " . $endFunction ; }
                    elsif ($endType eq "unit") { $endFunction = "Result_unit " . $endFunction ; }
                    elsif ($endType eq "SExpRec_pointer") { $endFunction = "Result_pointer " . $endFunction ; }
                    else { die "Should not happen." ; }

                    while ($acc =~ /(nat|int|unit|SExpRec_pointer) -> $/){
                        my $argType = $1 ;
                        $acc =~ s/(nat|int|unit|SExpRec_pointer) -> $// ;

                        if ($argType eq "nat") { $endFunction = "Argument_int (" . $endFunction . ")" ; }
                        elsif ($argType eq "int") { $endFunction = "Argument_float (" . $endFunction . ")" ; }
                        elsif ($argType eq "unit") { $endFunction = "Argument_unit (" . $endFunction . ")" ; }
                        elsif ($argType eq "SExpRec_pointer") { $endFunction = "Argument_pointer (" . $endFunction . ")" ; }
                        else { die "Should not happen." ; }
                    }

                    print $mlStream "(\"" . $funName . "\", " . $endFunction . ") ::\n" ;
                }
            }
        }
        # THe next line will be checked in the next iteration.
        $acc = $row ;
    } else {
        # The previous line was not complete.
        $acc .= $row ;
    }
}

print $mlStream "[]\n" ;
close $mlStream ;

print "Cleaning up…\n" ;

if (not $fileExist) {
    unlink $coqFile ;
}

print "Done.\n" ;

