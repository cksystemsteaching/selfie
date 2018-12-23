#!/usr/bin/perl -l

use strict;
use Cwd;
use POSIX qw( WNOHANG );
use File::Basename;

#CONSTANTS
use constant TIME_TO_WAIT => 20; #wait 10 seconds per test

#Variables
my $input_to_test;
my $FileLog;
my $selfie = "selfie";

my $has_error = 0;
my $nb_test = 0;

#BEGIN
die "needs: the test folder emplacement" if (@ARGV < 1);
$input_to_test = shift(@ARGV);
#generalize ?
#our @goods = glob "test/goods/*";
#our @wrongs = glob "test/wrongs/*";

#Set fileLog
sub create_log {
  my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime();
  #printf("Time Format - HH:MM:SS ");
  #printf("%02d:%02d:%02d\n", $hour, $min, $sec);
  $FileLog = "log_$year.$mon.$hour.$min.$sec.txt";
  print "Log file in $FileLog";
}

#Parse test directories and execute the test routines
#@arg[in] the directory name
sub find_test {
    my $d = shift;
    return if ($d =~ /\./ || $d =~ /\.\./);

    opendir (my $dh, "$d") or die "Can't open dir $d: $!\n";

    my @other_d = ();
    #Parse directory's files
    while (my $f = readdir ($dh)) {
	     do {exec_test("$d/$f"); next} if (-f "$d/$f") && ("$f" =~ /\.c/); #test the .c files
       #do {print"$d/$f"; next} if ("$f" !~ /.+-.+\.txt/) && ("$f" =~ /\.txt/);
	     push @other_d, "$d/$f" if -d "$d/$f"; #record sub-dirs
    }
    closedir($dh);

    ##rec for all sub-dirs
    foreach my $d (@other_d) {&find_test ("$d");}
}

#Parse test header
#@arg[in] test file name
sub handleTestPrologue {
  my $file = shift;
  my @out;
  my %return_codes;

  my $prolog = `head -1 $file`;
  chomp($prolog);

  # \w means the 63 characters [A-Za-z0-9_]
  if ( $prolog =~ m|\s*//\s*\[([\w\- \./;<>,]+)\]| ) {
    my @tmp = split(';', $1);

    push @out, (shift @tmp); #cmd_arg

    #<exit line, w-start, w-end, step> or <branch line, unreachable case>
    for my $tuple (@tmp) {
      my @items = split(',', $tuple);
      push @{$return_codes{substr($items[0], 1)}}, $tuple; #{line} => ref_to_@["<line,start,end, step>" or "<line,label>"]
    }

    push (@out, \%return_codes); #[cmd, %{line}{@<expected_values>}

    #debug
    #for my $i (@out) {print "item: $i"};
    return @out;

  } else {die "Match fail for $file ($prolog)"}
}

sub exec_test {
  my $testFile = shift;
  my ($cmd_args, $return_codes) = handleTestPrologue($testFile);

  my $dir = dirname($testFile);
  my $base = basename($testFile, ".c");

  #fails if selfie -c <file>.c does not match the test file name
  die "$testFile <> $cmd_args" if ( -1 == index($cmd_args, $testFile) );

#  my $Testoutput = $dir . "/" . $base . ".out";
  my $testOutput = "/tmp/" . $base . ".out";

  `echo "~~~--~~~------~~~---~~~ $testFile:" 2>&1 >> $FileLog`;
  my $testCmd = "./$selfie " . $cmd_args; #create the command

  print "run $testCmd";

  # ---> heavy stuff but working in case of infinite loops
  # test and killed if too long
  my $pid = fork();
  die "cannot fork" unless defined $pid;

  if(0 == $pid) {
    my $command = "$testCmd 2>&1 > $testOutput";

    local $SIG{ALRM} = sub { `echo "KILLED" >> $FileLog`; exit(-1); }; #avoid parent freezed forever ...
    alarm TIME_TO_WAIT; #5 seconds

    `$command`; #execute

    exit(0);
  }

  my $r_pid = 0;
  while($r_pid <= 0) {
    $r_pid = waitpid($pid, "WNOHANG");
    die "error with $pid" if ($r_pid < 0);

    if(0 == $r_pid) { #never happend
      sleep(TIME_TO_WAIT); #TIME_TO_WAIT seconds to finish
      my $time_waited = kill(15, $pid);
      #kill -- -$PGID
      print "kill $pid after $time_waited second(s)!";
    }
  }
  # ---> heavy stuff but working in case of infinite loops
  `pkill selfie`; # kill grandchild commands

  #die "error in test execution" if($?); (needs good return 0)

  ###Check
  if(&verifyOutcomes($testOutput, $return_codes)) {
    `echo "PASS" >> $FileLog`;
  } else {
    `echo "WRONG" >> $FileLog`;
    $has_error = 1;
  }
  ###Check

  unlink $testOutput or die " Could not unlink $testOutput: $!";
  $nb_test++;

  `echo "- - - - - - -" >> $FileLog`;
}

sub verifyUnreachableLine {
  my $expected_array  = shift;
  my $r_label         = shift;
  my $hasmatch = 0;

  foreach my $expected_line (@$expected_array) {
    if($expected_line =~ /\<\d+,(\w+)\>/) {
      return 1 if($r_label eq $1);
      $hasmatch = 1;
    }
  }

  die "cannot read expected w-values" unless $hasmatch;
  return 0;
}

sub verifyExitLine {
  my $expected_array  = shift;
  my $r_start         = shift;
  my $r_end           = shift;
  my $r_step          = shift;
  my $hasmatch = 0;

  foreach my $expected_line (@$expected_array) {
    if($expected_line =~ /\<\d+,(-?\d+),(-?\d+),(-?\d+)\>/) {
      return 1 if(($1 == $r_start) && ($2 == $r_end) && ($3 == $r_step));
      $hasmatch = 1;
    }
  }

  die "cannot read expected w-values" unless $hasmatch;
  return 0;
}

sub verifyOutcomes {
  my $file = shift;
  my $results = shift;
  my %hash = %{$results};
  my $check = 0;

  foreach my $ref_to_arrays (values %hash) { #should have nb_hash exit points
    $check += scalar @$ref_to_arrays;
  }

  open (REAL, "<$file") or die "Can't open $file : $!\n";
  while(<REAL>) {
    #exit case (or exception)
    if(/reaching end point at: \w+\(~(\d+)\) with exit code \<(-?\d+),(-?\d+),(-?\d+)\>/) {
        my $r_line  = $1;
        my $r_start = $2;
        my $r_end   = $3;
        my $r_step  = $4;

        die "line not expected" unless(exists($hash{$r_line}));
        my $expected_values = join " | ", @{$hash{$r_line}};
        `echo "At line $r_line is <$r_start, $r_end, $r_step> == $expected_values?" >> $FileLog`;

        return 0 unless(&verifyExitLine($hash{$r_line}, $r_start, $r_end, $r_step));
        `echo ". . . ok!" >> $FileLog`;
        $check --;

        #unreachable case
    } elsif(/LINE:\(~(\d+)\)\] branch "(\w+)" unreachable/) {
        my $r_line  = $1;
        my $r_label = $2;

        die "line not expected" unless(exists($hash{$r_line}));
        my $expected_values = join " | ", @{$hash{$r_line}};
        `echo "At line $r_line is $r_label == $expected_values?" >> $FileLog`;

        return 0 unless(&verifyUnreachableLine($hash{$r_line}, $r_label));
        `echo ". . . ok!" >> $FileLog`;
        $check --;
    }
  }
  close REAL;
  `echo "MISSING cases" >> $FileLog` unless 0 == $check;
  return 0 == $check; #false if check != nb_hash
}

#Main
&create_log();

if ("$input_to_test" =~ /[^-]+\.c/) { #exec if file
  exec_test("$input_to_test");
} else {
  $input_to_test = `pwd` if ($input_to_test =~ /\./);
  chomp $input_to_test;
  chop $input_to_test if (substr($input_to_test, -1) eq "/");

  &find_test ($input_to_test) if -d $input_to_test;
}

`echo "$nb_test test(s) executed" >> $FileLog`;
die "Test(s) failed" if($has_error);
exit(0);
