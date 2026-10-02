#!/bin/bash


# On CPU
for n in 16 32 64 128 256 512 1024 2048 4096 8192 16384
do
    python3 speed_dct.py \
        --n $n \
        --device "cpu"
done


# On GPU
for n in 16 32 64 128 256 512 1024 2048 4096 8192 16384
do
    python3 speed_dct.py \
        --n $n \
        --b 1 \
        --device "cuda"
done

# With batches
for n in 16 32 64 128 256 512 1024 2048 4096 8192 16384
do
    for b in 16 32 64 128 256 512 1024 2048 4096 8192 16384 32768
    do
        python3 speed_dct.py \
            --n $n \
            --b $b \
            --device "cuda"
    done
done