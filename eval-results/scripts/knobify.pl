# usage: perl knobify.pl FILE GROUP
my ($file, $group) = @ARGV;
open my $fh, '<', $file or die; local $/; my $s = <$fh>; close $fh;
my @names;
$s =~ s{^(\s*)(pub\(crate\) |pub )?const ([A-Z][A-Z0-9_]*): bool = true;}{
  push @names, $3; my $v = $2 // ''; $v =~ s/ $//;
  "$1crate::knob!($v $3, \"" . lc($3) . "\", \"$group\");"
}gme;
for my $n (@names) {
  # replace uses not already followed by '(' and not inside the knob! line
  my @lines = split /\n/, $s, -1;
  for (@lines) { next if /crate::knob!\(.*\b$n\b/; s/\b$n\b(?!\()/$n()/g; }
  $s = join "\n", @lines;
}
open $fh, '>', $file or die; print $fh $s; close $fh;
print "$file: ", scalar(@names), " knobs: @names\n";
