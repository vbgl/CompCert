set term png
set output 'bench.png'

set datafile separator ','
set key autotitle columnhead

set style data histogram
set style fill solid
set xtic rotate

set key top center

set yrange [0: 0.3]

plot 'results' using 2:xticlabels(1), '' using 3

