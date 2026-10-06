# Grouped bars: wasm interp, weval, NightMonkey, native Ion per benchmark,
# normalized to native Ion = 1.0 (higher is better). Geomean is the
# rightmost group.
#
#   gnuplot -e "scale='lin'" vs_ion.gp
#   gnuplot -e "scale='log'" vs_ion.gp
#   (add -e "fmt='png'" for PNG instead of SVG)

if (!exists("scale")) scale = 'lin'
if (!exists("fmt")) fmt = 'svg'

if (fmt eq 'png') {
    set terminal pngcairo size 1600,700 font "Inter,15" background rgb "#fcfcfb"
} else {
    set terminal svg size 1600,700 dynamic font "Inter,15" background rgb "#fcfcfb"
}
set output sprintf("vs_ion_%s.%s", scale, fmt)

# Palette: categorical slots 1-4, fixed order (validated; light surface).
c_interp = "#2a78d6"   # wasm interp
c_weval  = "#eb6834"   # weval
c_nm     = "#1baf7a"   # NightMonkey
c_ion    = "#eda100"   # native Ion
ink      = "#1f1f1e"
ink2     = "#5c5b55"
grid     = "#e4e3dd"

set datafile commentschars "#"
set style data histograms
set style histogram clustered gap 1.4
# Thin dark outline: relief for the two sub-3:1 fills (aqua, yellow).
set style fill solid 1.0 border rgb ink2
set boxwidth 0.86 relative

set border 3 lc rgb ink2 lw 1
set tics nomirror tc rgb ink2
set xtics scale 0 rotate by -35 offset -0.6,0 tc rgb ink
set grid ytics lc rgb grid lw 1 dt 1
set grid noxtics
set key top left horizontal reverse Left samplen 1.0 spacing 1.1 width 3 maxcols 4 tc rgb ink opaque box lc rgb "#fcfcfb"
set bmargin 6.5
set xrange [-0.6:13.6]

# Separate the geomean group from the benchmarks.
set arrow 1 from 12.5, graph 0 to 12.5, graph 1 nohead lc rgb ink2 dt 3 lw 1

if (scale eq 'log') {
    set logscale y 10
    set yrange [0.005:2.2]
    set ytics ("0.01" 0.01, "0.03" 0.03, "0.1" 0.1, "0.3" 0.3, "1" 1) tc rgb ink2
    set ylabel "Score relative to native Ion (log scale; higher is better)" tc rgb ink2
    set title "Octane + React: wasm engines vs native Ion (log scale)" tc rgb ink font ",18"
    lblfmt = "%.2f"
} else {
    set yrange [0:1.18]
    set ytics 0.2 tc rgb ink2
    set ylabel "Score relative to native Ion (higher is better)" tc rgb ink2
    set title "Octane + React: wasm engines vs native Ion" tc rgb ink font ",18"
    lblfmt = "%.2f"
}
# Ion = 1.0 reference line.
set arrow 2 from graph 0, first 1 to graph 1, first 1 nohead lc rgb ink dt 2 lw 1 back

# Direct labels on the geomean group only (row 13, 0-based).
off(i) = 13 + (i - 1.5) * (1.0 / 5.4)
lab(c) = sprintf(lblfmt, c)

plot 'vs_ion.dat' using 2:xtic(1) title "wasm interp" lc rgb c_interp, \
     ''            using 3          title "weval"       lc rgb c_weval, \
     ''            using 4          title "NightMonkey" lc rgb c_nm, \
     ''            using 5          title "native Ion"  lc rgb c_ion, \
     ''            every ::13::13 using (off(0)):2:(lab($2)) with labels offset -0.4,0.7 tc rgb ink font ",12" notitle, \
     ''            every ::13::13 using (off(1)):3:(lab($3)) with labels offset 0.2,1.4 tc rgb ink font ",12" notitle, \
     ''            every ::13::13 using (off(2)):4:(lab($4)) with labels offset 0,0.7 tc rgb ink font ",12" notitle, \
     ''            every ::13::13 using (off(3)):5:(lab($5)) with labels offset 0,0.7 tc rgb ink font ",12" notitle
