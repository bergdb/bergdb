bergdb-workload 1
# Gen seed=31 n=4 keys=81 maxnode=8 sd=300 retain=1 restarts=1 valmax=235 big=5 del=19 long=39 empty=2 huge=3 setters=1 reads=1
set maxnode 8
set sd 300
set retain 10000000
clock 229995
t 629995 d /missing/0 p /k/38 x:04ef0382a67e19a6b7966c88d2d8e3ee8bff27d6bea60a1924a147fb4b0000ab03a17605208f5f403850a627b6f2bc3ebb64f30dbd3c6f446b7bbb7c051acc31482eb532d6605eccbade65846fbdec7a1cb76386e30459c3cad1bf3e13100aca3c
setsd 1063
t 1229995 p /k/5 s:fdouacmnzvljqyxuwsafbbthxywjgxtntlqpsklfyifhmzpkidnmyoyztbnjzargvpgofpig
check latest
check 856460
get latest /long/abcdefghijklmnopqrstuv/75 /k/49 /long/abcdefghijklmnopqrs/18 /%C3%BCml/51 /k/18 /long/abcdefghij/9 /k/33 /long/abcdefghijklmnopq/16 /k/26 /k/77
get 945370 /k/48 /k/48 /long/abcdefghijklmnopqrstuvwxyz/25 /long/abcdefghijklmnopqrstuvwxyz0123456/32 /k/24 /k/64 /long/abcdefghi/62 /long/abcdefghijklmn/13 /k/28 /long/abcd/57
t 2429995 p /long/abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKL/47 r:2598960391614508834:78 d /k/46
t 4329995 p /k/49 s:qhdzlbrezfiydrocslsjvoodlpznnsrgovkszsxumwtghbammwccnxzanaraqtfskgbbzvdrlrglwojgvmctyy p /k/77 r:5075998652338627526:105 p /long/abcdefghijklmnopq/16 r:2033741454958944082:230
sync
restart
check latest
sync
