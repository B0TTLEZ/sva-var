# cd /data/sva-var/rtl_analyzer/analyzer_cpp
# cmake --build build -j8
# ./build/analyzer
cd /data/sva-var/rtl_analyzer/analyzer_cpp
cmake -B build
cmake --build build
cmake --build build -j8
./build/analyzer