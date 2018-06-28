#!/usr/bin/perl -l

use strict;
use Cwd;
use POSIX qw( WNOHANG );
use File::Basename;

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
  printf("Time Format - HH:MM:SS ");
  printf("%02d:%02d:%02d\n", $hour, $min, $sec);
  $FileLog = "log_$year.$mon.$hour.$min.$sec.txt";
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

    #<exit line, w-start, w-end, step>
    for my $quadruple (@tmp) {
      my @items = split(',', $quadruple);
      $return_codes{substr($items[0], 1)} = $quadruple; #{line} => "<line,start,end, step>"
    }

    push (@out, \%return_codes); #hash of line->quadruple

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
  my $testCmd = "./$selfie -test " . $cmd_args; #create the command

  print "run $testCmd";

  # ---> heavy stuff but working in case of infinite loops
  # test and killed if too long
  my $pid = fork();
  die "cannot fork" unless defined $pid;

  if(0 == $pid) {
    my $command = "$testCmd 2>&1 > $testOutput";

    local $SIG{ALRM} = sub { `echo "KILLED" >> $FileLog`; exit(-1); }; #avoid parent freezed forever ...
    alarm 1; #1 second

    `$command`; #execute

    exit(0);
  }

  my $r_pid = 0;
  while($r_pid <= 0) {
    $r_pid = waitpid($pid, "WNOHANG");
    die "error with $pid" if ($r_pid < 0);

    if(0 == $r_pid) { #never happend
      sleep(1); #1 second to finish
      kill(15, $pid);
      #kill -- -$PGID
      print "kill $pid! ";
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

sub verifyOutcomes {
  my $file = shift;
  my $results = shift;
  my %hash = %{$results};
  my $check = 0;

  open (REAL, "<$file") or die "Can't open $file : $!\n";
  while(<REAL>) {
    if(/reaching end point at:\w+\(~(\d+)\) with exit code \<(-?\d+),(-?\d+),(-?\d+)\>/) {
        my $r_line  = $1;
        my $r_start = $2;
        my $r_end   = $3;
        my $r_step  = $4;

        die "line not expected" unless(exists($hash{$r_line}));
        `echo "At line $r_line is <$r_start, $r_end, $r_step> == $hash{$r_line}?" >> $FileLog`;

        if($hash{$r_line} =~ /\<\d+,(-?\d+),(-?\d+),(-?\d+)\>/) {
          return 0 unless(($1 == $r_start) && ($2 == $r_end) && ($3 == $r_step));
        } else {die "cannot read expected w-values";}
        $check ++;
    }
  }
  close REAL;
  return $check; #false if no check
}

#Main
&create_log();

do {exec_test("$input_to_test"); next} if "$input_to_test" =~ /[^-]+.c/; #exec if file
$input_to_test = `pwd` if ($input_to_test =~ /\./);
chomp $input_to_test;

&find_test ($input_to_test) if -d $input_to_test;

`echo "$nb_test tests executed" >> $FileLog`;

exit(-1) if($has_error);
exit(0);
