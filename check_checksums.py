#!/usr/bin/env python3

def main(fname):

    with open(fname) as fid:
        for line in fid:
            if line.startswith('   '):
                parts = line.strip().split(' ')
                if len(parts[0]) != 3:
                    raise ValueError(f'bad checksum in {line}')

if __name__ == "__main__":
    main('pages/checksums.rst')
                
