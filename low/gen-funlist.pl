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


print "Creating $mlFile…\n" ;

unlink $mlFile if -f $mlFile ;

open (my $mlStream, '>', $mlFile) or die "Could not create file $mlFile for some reason." ;
print $mlStream "(* This file has been automatically generated. *)\n" ;
print $mlStream "(* This file is meant to be rewritten at each compilation: save your changes elsewhere if you really want to edit it. *)\n" ;
print $mlStream "open Low\n" ;
print $mlStream "open DebugType\n" ;
print $mlStream "let funlist =\n" ;

my $exitedBecauseOfError = $true ;

END {
    if ($exitedBecauseOfError) {
        print "The generation failed for some reason."
            . " Generating a dummy file instead."
            . " Some features will be absent from the final program." ;
        print $mlStream "[]\n" ;
        print $mlStream "let _ = prerr_endline \"Warning: "
            . "the generation of the file $mlFile failed for some reason."
            . " Some features are absent from this program."
            . " To investigate on the issue, you may remove the file $mlFile and recompile the project.\"\n" ;
        close $mlStream ;
    }

    # A quick clean-up.
    if (not $fileExist) {
        unlink $coqFile ;
    }
}


print "Generating Coq file…\n" ;

if ($fileExist) {
    print "Coq file already there, using it as-is.\n"
} else {
    open (my $outStream, '>', $coqFile) or die "Could not create file $coqFile for some reason." ;
    print $outStream "(* This file has been automatically generated. *)\n" ;
    print $outStream "Require Import Rinit Rparsing.\n" ;
    print $outStream "SearchAbout result.\n" ;
    close $outStream ;
}

print "Executing Coq file…\n" ;

open (PIPE, "cat low/funlist.v |"
    . "coqtop -R ./lib Lib -R ./lib/tlc/src TLC -R ./low Low -noglob -quiet |")
    or die "Can’t execute Coq for some reason." ;

print "Translating output to $mlFile…\n" ;

my $acc = "" ;

sub check {
    my ($name) = @_ ;
    my $nameMaj = $name ;
    $nameMaj =~ s/^([A-Z])/\L$1/ ;
    # This function checks whether a given function has been extracted into OCaml by Coq.
    open (FILE, $extractedFile) or die "Unable to open file $extractedFile for some reason." ;
    while (<FILE>){
        if (/^val $name :/) {
            close FILE ;
            return $name ;
        } elsif (/^val $nameMaj :/) {
            close FILE ;
            return $nameMaj ;
        }
    }
    close FILE ;
    return "" ;
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

            if ($acc =~ /^ state ->( (unit|bool|nat|int|float|SExpRec_pointer) ->)* result (unit|bool|nat|int|float|string|SExpRec_pointer)/){
                # This function is of interest for us.
                $acc =~ s/^ state ->// ;

                # Checking that it has indeed been extracted.
                my $camlName = check ($funName) ;
                if (not ($camlName eq "")) {

                    my $beginFunction = "(fun " ;
                    if ($useGlobals) { $beginFunction .= "g " ; } else { $beginFunction .= "_ " ; }
                    if ($useRuns) { $beginFunction .= "r " ; } else { $beginFunction .= "_ " ; }
                    $beginFunction .= "s -> " ;
                    $beginFunction .= $camlName ;
                    if ($useGlobals) { $beginFunction .= " g" ; }
                    if ($useRuns) { $beginFunction .= " r" ; }
                    $beginFunction .= " s" ;

                    my $endFunction = ")" ;

                    $acc =~ /result (unit|bool|nat|int|float|string|SExpRec_pointer)$/ ;
                    my $endType = $1 ;
                    $acc =~ s/result .*//g ;

                    if ($endType eq "unit") { $beginFunction = "Result_unit " . $beginFunction ; }
                    elsif ($endType eq "bool") { $beginFunction = "Result_bool " . $beginFunction ; }
                    elsif ($endType eq "int" or $endType eq "nat") { $beginFunction = "Result_int " . $beginFunction ; }
                    elsif ($endType eq "float") { $beginFunction = "Result_float " . $beginFunction ; }
                    elsif ($endType eq "string") { $beginFunction = "Result_string " . $beginFunction ; }
                    elsif ($endType eq "SExpRec_pointer") { $beginFunction = "Result_pointer " . $beginFunction ; }
                    else { die "Unknown result type: " . $endType . ". This should not happen." ; }

                    my $argNum = 0 ;

                    while ($acc =~ /(unit|bool|nat|int|float|SExpRec_pointer) -> $/){
                        my $argType = $1 ;
                        $acc =~ s/(unit|bool|nat|int|float|SExpRec_pointer) -> $// ;
                        $argNum += 1 ;

                        if ($argType eq "unit") {
                            $beginFunction = "Argument_unit (fun _ -> " . $beginFunction ;
                            $endFunction = " ()" . $endFunction ;
                        } elsif ($argType eq "bool") {
                            $beginFunction = "Argument_bool (fun b" . $argNum . " -> " . $beginFunction ;
                            $endFunction = " b" . $argNum . $endFunction ;
                        } elsif ($argType eq "nat") {
                            $beginFunction = "Argument_int (fun n" . $argNum . " -> " . $beginFunction ;
                            $endFunction = " n" . $argNum . $endFunction ;
                        } elsif ($argType eq "int") {
                            $beginFunction = "Argument_float (fun i" . $argNum . " -> " . $beginFunction ;
                            $endFunction = " i" . $argNum . $endFunction ;
                        } elsif ($argType eq "float") {
                            $beginFunction = "Argument_float (fun f" . $argNum . " -> " . $beginFunction ;
                            $endFunction = " f" . $argNum . $endFunction ;
                        } elsif ($argType eq "SExpRec_pointer") {
                            $beginFunction = "Argument_pointer (fun p" . $argNum . " -> " . $beginFunction ;
                            $endFunction = " p" . $argNum . $endFunction ;
                        } else { die "Unknown argument type: " . $argType . ". This should not happen." ; }

                        $endFunction .= ")" ;
                    }

                    print $mlStream "(\"" . $funName . "\", " . $beginFunction . $endFunction . ") ::\n" ;
                }
            }
        }
        # The next line will be checked in the next iteration.
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

$exitedBecauseOfError = $false ;
print "Done.\n" ;

