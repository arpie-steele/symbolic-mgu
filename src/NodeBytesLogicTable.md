| node | arity | func | `u8` code |
| ---- | ----- | ---- | --------- |
| `F00` | 0 | `0` | 0x00 |
| `F01` | 3 | `!(a | b | c)` | 0x01 |
| `F02` | 3 | `a ^ a & b ^ a & c ^ a & b & c` | 0x02 |
| `F03` | 3 | `1 ^ b ^ c ^ b & c` | 0x03 |
| `F04` | 3 | `b ^ a & b ^ b & c ^ a & b & c` | 0x04 |
| `F05` | 3 | `1 ^ a ^ c ^ a & c` | 0x05 |
| `F06` | 3 | `a ^ b ^ a & c ^ b & c` | 0x06 |
| `F07` | 3 | `1 ^ a & b ^ c ^ a & b & c` | 0x07 |
| `F08` | 3 | `a & b ^ a & b & c` | 0x08 |
| `F09` | 3 | `1 ^ a ^ b ^ c ^ a & c ^ b & c` | 0x09 |
| `F0A` | 3 | `a ^ a & c` | 0x0a |
| `F0B` | 3 | `1 ^ b ^ a & b ^ c ^ b & c ^ a & b & c` | 0x0b |
| `F0C` | 3 | `b ^ b & c` | 0x0c |
| `F0D` | 3 | `1 ^ a ^ a & b ^ c ^ a & c ^ a & b & c` | 0x0d |
| `F0E` | 3 | `a ^ b ^ a & b ^ a & c ^ b & c ^ a & b & c` | 0x0e |
| `F0F` | 3 | `!c` | 0x0f |
| `F10` | 3 | `c ^ a & c ^ b & c ^ a & b & c` | 0x10 |
| `F11` | 2 | `!(a | b)` | 0x11 |
| `F12` | 3 | `a ^ a & b ^ c ^ b & c` | 0x12 |
| `F13` | 3 | `1 ^ b ^ a & c ^ a & b & c` | 0x13 |
| `F14` | 3 | `b ^ a & b ^ c ^ a & c` | 0x14 |
| `F15` | 3 | `1 ^ a ^ b & c ^ a & b & c` | 0x15 |
| `F16` | 3 | `a ^ b ^ c ^ a & b & c` | 0x16 |
| `F17` | 3 | `1 ^ a & b ^ a & c ^ b & c` | 0x17 |
| `F18` | 3 | `a & b ^ c ^ a & c ^ b & c` | 0x18 |
| `F19` | 3 | `1 ^ a ^ b ^ a & b & c` | 0x19 |
| `F1A` | 3 | `a ^ c ^ b & c ^ a & b & c` | 0x1a |
| `F1B` | 3 | `1 ^ b ^ a & b ^ a & c` | 0x1b |
| `F1C` | 3 | `b ^ c ^ a & c ^ a & b & c` | 0x1c |
| `F1D` | 3 | `1 ^ a ^ a & b ^ b & c` | 0x1d |
| `F1E` | 3 | `a ^ b ^ a & b ^ c` | 0x1e |
| `F1F` | 3 | `1 ^ a & c ^ b & c ^ a & b & c` | 0x1f |
| `F20` | 3 | `a & c ^ a & b & c` | 0x20 |
| `F21` | 3 | `1 ^ a ^ b ^ a & b ^ c ^ b & c` | 0x21 |
| `F22` | 2 | `a & !b` | 0x22 |
| `F23` | 3 | `1 ^ b ^ c ^ a & c ^ b & c ^ a & b & c` | 0x23 |
| `F24` | 3 | `b ^ a & b ^ a & c ^ b & c` | 0x24 |
| `F25` | 3 | `1 ^ a ^ c ^ a & b & c` | 0x25 |
| `F26` | 3 | `a ^ b ^ b & c ^ a & b & c` | 0x26 |
| `F27` | 3 | `1 ^ a & b ^ c ^ a & c` | 0x27 |
| `F28` | 3 | `a & b ^ a & c` | 0x28 |
| `F29` | 3 | `1 ^ a ^ b ^ c ^ b & c ^ a & b & c` | 0x29 |
| `F2A` | 3 | `a ^ a & b & c` | 0x2a |
| `F2B` | 3 | `1 ^ b ^ a & b ^ c ^ a & c ^ b & c` | 0x2b |
| `F2C` | 3 | `b ^ a & c ^ b & c ^ a & b & c` | 0x2c |
| `F2D` | 3 | `1 ^ a ^ a & b ^ c` | 0x2d |
| `F2E` | 3 | `a ^ b ^ a & b ^ b & c` | 0x2e |
| `F2F` | 3 | `1 ^ c ^ a & c ^ a & b & c` | 0x2f |
| `F30` | 3 | `c ^ b & c` | 0x30 |
| `F31` | 3 | `1 ^ a ^ b ^ a & b ^ a & c ^ a & b & c` | 0x31 |
| `F32` | 3 | `a ^ a & b ^ c ^ a & c ^ b & c ^ a & b & c` | 0x32 |
| `F33` | 2 | `!b` | 0x33 |
| `F34` | 3 | `b ^ a & b ^ c ^ a & b & c` | 0x34 |
| `F35` | 3 | `1 ^ a ^ a & c ^ b & c` | 0x35 |
| `F36` | 3 | `a ^ b ^ c ^ a & c` | 0x36 |
| `F37` | 3 | `1 ^ a & b ^ b & c ^ a & b & c` | 0x37 |
| `F38` | 3 | `a & b ^ c ^ b & c ^ a & b & c` | 0x38 |
| `F39` | 3 | `1 ^ a ^ b ^ a & c` | 0x39 |
| `F3A` | 3 | `a ^ c ^ a & c ^ b & c` | 0x3a |
| `F3B` | 3 | `1 ^ b ^ a & b ^ a & b & c` | 0x3b |
| `F3C` | 3 | `b ^ c` | 0x3c |
| `F3D` | 3 | `1 ^ a ^ a & b ^ a & c ^ b & c ^ a & b & c` | 0x3d |
| `F3E` | 3 | `a ^ b ^ a & b ^ c ^ a & c ^ a & b & c` | 0x3e |
| `F3F` | 3 | `1 ^ b & c` | 0x3f |
| `F40` | 3 | `b & c ^ a & b & c` | 0x40 |
| `F41` | 3 | `1 ^ a ^ b ^ a & b ^ c ^ a & c` | 0x41 |
| `F42` | 3 | `a ^ a & b ^ a & c ^ b & c` | 0x42 |
| `F43` | 3 | `1 ^ b ^ c ^ a & b & c` | 0x43 |
| `F44` | 2 | `!a & b` | 0x44 |
| `F45` | 3 | `1 ^ a ^ c ^ a & c ^ b & c ^ a & b & c` | 0x45 |
| `F46` | 3 | `a ^ b ^ a & c ^ a & b & c` | 0x46 |
| `F47` | 3 | `1 ^ a & b ^ c ^ b & c` | 0x47 |
| `F48` | 3 | `a & b ^ b & c` | 0x48 |
| `F49` | 3 | `1 ^ a ^ b ^ c ^ a & c ^ a & b & c` | 0x49 |
| `F4A` | 3 | `a ^ a & c ^ b & c ^ a & b & c` | 0x4a |
| `F4B` | 3 | `1 ^ b ^ a & b ^ c` | 0x4b |
| `F4C` | 3 | `b ^ a & b & c` | 0x4c |
| `F4D` | 3 | `1 ^ a ^ a & b ^ c ^ a & c ^ b & c` | 0x4d |
| `F4E` | 3 | `a ^ b ^ a & b ^ a & c` | 0x4e |
| `F4F` | 3 | `1 ^ c ^ b & c ^ a & b & c` | 0x4f |
| `F50` | 3 | `c ^ a & c` | 0x50 |
| `F51` | 3 | `1 ^ a ^ b ^ a & b ^ b & c ^ a & b & c` | 0x51 |
| `F52` | 3 | `a ^ a & b ^ c ^ a & b & c` | 0x52 |
| `F53` | 3 | `1 ^ b ^ a & c ^ b & c` | 0x53 |
| `F54` | 3 | `b ^ a & b ^ c ^ a & c ^ b & c ^ a & b & c` | 0x54 |
| `F55` | 1 | `!a` | 0x55 |
| `F56` | 3 | `a ^ b ^ c ^ b & c` | 0x56 |
| `F57` | 3 | `1 ^ a & b ^ a & c ^ a & b & c` | 0x57 |
| `F58` | 3 | `a & b ^ c ^ a & c ^ a & b & c` | 0x58 |
| `F59` | 3 | `1 ^ a ^ b ^ b & c` | 0x59 |
| `F5A` | 3 | `a ^ c` | 0x5a |
| `F5B` | 3 | `1 ^ b ^ a & b ^ a & c ^ b & c ^ a & b & c` | 0x5b |
| `F5C` | 3 | `b ^ c ^ a & c ^ b & c` | 0x5c |
| `F5D` | 3 | `1 ^ a ^ a & b ^ a & b & c` | 0x5d |
| `F5E` | 3 | `a ^ b ^ a & b ^ c ^ b & c ^ a & b & c` | 0x5e |
| `F5F` | 3 | `1 ^ a & c` | 0x5f |
| `F60` | 3 | `a & c ^ b & c` | 0x60 |
| `F61` | 3 | `1 ^ a ^ b ^ a & b ^ c ^ a & b & c` | 0x61 |
| `F62` | 3 | `a ^ a & b ^ b & c ^ a & b & c` | 0x62 |
| `F63` | 3 | `1 ^ b ^ c ^ a & c` | 0x63 |
| `F64` | 3 | `b ^ a & b ^ a & c ^ a & b & c` | 0x64 |
| `F65` | 3 | `1 ^ a ^ c ^ b & c` | 0x65 |
| `F66` | 2 | `a ^ b` | 0x66 |
| `F67` | 3 | `1 ^ a & b ^ c ^ a & c ^ b & c ^ a & b & c` | 0x67 |
| `F68` | 3 | `a & b ^ a & c ^ b & c ^ a & b & c` | 0x68 |
| `F69` | 3 | `!(a ^ b ^ c)` | 0x69 |
| `F6A` | 3 | `a ^ b & c` | 0x6a |
| `F6B` | 3 | `1 ^ b ^ a & b ^ c ^ a & c ^ a & b & c` | 0x6b |
| `F6C` | 3 | `b ^ a & c` | 0x6c |
| `F6D` | 3 | `1 ^ a ^ a & b ^ c ^ b & c ^ a & b & c` | 0x6d |
| `F6E` | 3 | `a ^ b ^ a & b ^ a & b & c` | 0x6e |
| `F6F` | 3 | `1 ^ c ^ a & c ^ b & c` | 0x6f |
| `F70` | 3 | `c ^ a & b & c` | 0x70 |
| `F71` | 3 | `1 ^ a ^ b ^ a & b ^ a & c ^ b & c` | 0x71 |
| `F72` | 3 | `a ^ a & b ^ c ^ a & c` | 0x72 |
| `F73` | 3 | `1 ^ b ^ b & c ^ a & b & c` | 0x73 |
| `F74` | 3 | `b ^ a & b ^ c ^ b & c` | 0x74 |
| `F75` | 3 | `1 ^ a ^ a & c ^ a & b & c` | 0x75 |
| `F76` | 3 | `a ^ b ^ c ^ a & c ^ b & c ^ a & b & c` | 0x76 |
| `F77` | 2 | `!(a & b)` | 0x77 |
| `F78` | 3 | `a & b ^ c` | 0x78 |
| `F79` | 3 | `1 ^ a ^ b ^ a & c ^ b & c ^ a & b & c` | 0x79 |
| `F7A` | 3 | `a ^ c ^ a & c ^ a & b & c` | 0x7a |
| `F7B` | 3 | `1 ^ b ^ a & b ^ b & c` | 0x7b |
| `F7C` | 3 | `b ^ c ^ b & c ^ a & b & c` | 0x7c |
| `F7D` | 3 | `1 ^ a ^ a & b ^ a & c` | 0x7d |
| `F7E` | 3 | `a ^ b ^ a & b ^ c ^ a & c ^ b & c` | 0x7e |
| `F7F` | 3 | `!(a & b & c)` | 0x7f |
| `F80` | 3 | `a & b & c` | 0x80 |
| `F81` | 3 | `1 ^ a ^ b ^ a & b ^ c ^ a & c ^ b & c` | 0x81 |
| `F82` | 3 | `a ^ a & b ^ a & c` | 0x82 |
| `F83` | 3 | `1 ^ b ^ c ^ b & c ^ a & b & c` | 0x83 |
| `F84` | 3 | `b ^ a & b ^ b & c` | 0x84 |
| `F85` | 3 | `1 ^ a ^ c ^ a & c ^ a & b & c` | 0x85 |
| `F86` | 3 | `a ^ b ^ a & c ^ b & c ^ a & b & c` | 0x86 |
| `F87` | 3 | `1 ^ a & b ^ c` | 0x87 |
| `F88` | 2 | `a & b` | 0x88 |
| `F89` | 3 | `1 ^ a ^ b ^ c ^ a & c ^ b & c ^ a & b & c` | 0x89 |
| `F8A` | 3 | `a ^ a & c ^ a & b & c` | 0x8a |
| `F8B` | 3 | `1 ^ b ^ a & b ^ c ^ b & c` | 0x8b |
| `F8C` | 3 | `b ^ b & c ^ a & b & c` | 0x8c |
| `F8D` | 3 | `1 ^ a ^ a & b ^ c ^ a & c` | 0x8d |
| `F8E` | 3 | `a ^ b ^ a & b ^ a & c ^ b & c` | 0x8e |
| `F8F` | 3 | `1 ^ c ^ a & b & c` | 0x8f |
| `F90` | 3 | `c ^ a & c ^ b & c` | 0x90 |
| `F91` | 3 | `1 ^ a ^ b ^ a & b ^ a & b & c` | 0x91 |
| `F92` | 3 | `a ^ a & b ^ c ^ b & c ^ a & b & c` | 0x92 |
| `F93` | 3 | `1 ^ b ^ a & c` | 0x93 |
| `F94` | 3 | `b ^ a & b ^ c ^ a & c ^ a & b & c` | 0x94 |
| `F95` | 3 | `1 ^ a ^ b & c` | 0x95 |
| `F96` | 3 | `a ^ b ^ c` | 0x96 |
| `F97` | 3 | `1 ^ a & b ^ a & c ^ b & c ^ a & b & c` | 0x97 |
| `F98` | 3 | `a & b ^ c ^ a & c ^ b & c ^ a & b & c` | 0x98 |
| `F99` | 2 | `!(a ^ b)` | 0x99 |
| `F9A` | 3 | `a ^ c ^ b & c` | 0x9a |
| `F9B` | 3 | `1 ^ b ^ a & b ^ a & c ^ a & b & c` | 0x9b |
| `F9C` | 3 | `b ^ c ^ a & c` | 0x9c |
| `F9D` | 3 | `1 ^ a ^ a & b ^ b & c ^ a & b & c` | 0x9d |
| `F9E` | 3 | `a ^ b ^ a & b ^ c ^ a & b & c` | 0x9e |
| `F9F` | 3 | `1 ^ a & c ^ b & c` | 0x9f |
| `FA0` | 3 | `a & c` | 0xa0 |
| `FA1` | 3 | `1 ^ a ^ b ^ a & b ^ c ^ b & c ^ a & b & c` | 0xa1 |
| `FA2` | 3 | `a ^ a & b ^ a & b & c` | 0xa2 |
| `FA3` | 3 | `1 ^ b ^ c ^ a & c ^ b & c` | 0xa3 |
| `FA4` | 3 | `b ^ a & b ^ a & c ^ b & c ^ a & b & c` | 0xa4 |
| `FA5` | 3 | `1 ^ a ^ c` | 0xa5 |
| `FA6` | 3 | `a ^ b ^ b & c` | 0xa6 |
| `FA7` | 3 | `1 ^ a & b ^ c ^ a & c ^ a & b & c` | 0xa7 |
| `FA8` | 3 | `a & b ^ a & c ^ a & b & c` | 0xa8 |
| `FA9` | 3 | `1 ^ a ^ b ^ c ^ b & c` | 0xa9 |
| `FAA` | 1 | `a` | 0xaa |
| `FAB` | 3 | `1 ^ b ^ a & b ^ c ^ a & c ^ b & c ^ a & b & c` | 0xab |
| `FAC` | 3 | `b ^ a & c ^ b & c` | 0xac |
| `FAD` | 3 | `1 ^ a ^ a & b ^ c ^ a & b & c` | 0xad |
| `FAE` | 3 | `a ^ b ^ a & b ^ b & c ^ a & b & c` | 0xae |
| `FAF` | 3 | `1 ^ c ^ a & c` | 0xaf |
| `FB0` | 3 | `c ^ b & c ^ a & b & c` | 0xb0 |
| `FB1` | 3 | `1 ^ a ^ b ^ a & b ^ a & c` | 0xb1 |
| `FB2` | 3 | `a ^ a & b ^ c ^ a & c ^ b & c` | 0xb2 |
| `FB3` | 3 | `1 ^ b ^ a & b & c` | 0xb3 |
| `FB4` | 3 | `b ^ a & b ^ c` | 0xb4 |
| `FB5` | 3 | `1 ^ a ^ a & c ^ b & c ^ a & b & c` | 0xb5 |
| `FB6` | 3 | `a ^ b ^ c ^ a & c ^ a & b & c` | 0xb6 |
| `FB7` | 3 | `1 ^ a & b ^ b & c` | 0xb7 |
| `FB8` | 3 | `a & b ^ c ^ b & c` | 0xb8 |
| `FB9` | 3 | `1 ^ a ^ b ^ a & c ^ a & b & c` | 0xb9 |
| `FBA` | 3 | `a ^ c ^ a & c ^ b & c ^ a & b & c` | 0xba |
| `FBB` | 2 | `a | !b` | 0xbb |
| `FBC` | 3 | `b ^ c ^ a & b & c` | 0xbc |
| `FBD` | 3 | `1 ^ a ^ a & b ^ a & c ^ b & c` | 0xbd |
| `FBE` | 3 | `a ^ b ^ a & b ^ c ^ a & c` | 0xbe |
| `FBF` | 3 | `1 ^ b & c ^ a & b & c` | 0xbf |
| `FC0` | 3 | `b & c` | 0xc0 |
| `FC1` | 3 | `1 ^ a ^ b ^ a & b ^ c ^ a & c ^ a & b & c` | 0xc1 |
| `FC2` | 3 | `a ^ a & b ^ a & c ^ b & c ^ a & b & c` | 0xc2 |
| `FC3` | 3 | `1 ^ b ^ c` | 0xc3 |
| `FC4` | 3 | `b ^ a & b ^ a & b & c` | 0xc4 |
| `FC5` | 3 | `1 ^ a ^ c ^ a & c ^ b & c` | 0xc5 |
| `FC6` | 3 | `a ^ b ^ a & c` | 0xc6 |
| `FC7` | 3 | `1 ^ a & b ^ c ^ b & c ^ a & b & c` | 0xc7 |
| `FC8` | 3 | `a & b ^ b & c ^ a & b & c` | 0xc8 |
| `FC9` | 3 | `1 ^ a ^ b ^ c ^ a & c` | 0xc9 |
| `FCA` | 3 | `(a & c) | (!a & b)` | 0xca |
| `FCB` | 3 | `1 ^ b ^ a & b ^ c ^ a & b & c` | 0xcb |
| `FCC` | 2 | `b` | 0xcc |
| `FCD` | 3 | `1 ^ a ^ a & b ^ c ^ a & c ^ b & c ^ a & b & c` | 0xcd |
| `FCE` | 3 | `a ^ b ^ a & b ^ a & c ^ a & b & c` | 0xce |
| `FCF` | 3 | `1 ^ c ^ b & c` | 0xcf |
| `FD0` | 3 | `c ^ a & c ^ a & b & c` | 0xd0 |
| `FD1` | 3 | `1 ^ a ^ b ^ a & b ^ b & c` | 0xd1 |
| `FD2` | 3 | `a ^ a & b ^ c` | 0xd2 |
| `FD3` | 3 | `1 ^ b ^ a & c ^ b & c ^ a & b & c` | 0xd3 |
| `FD4` | 3 | `b ^ a & b ^ c ^ a & c ^ b & c` | 0xd4 |
| `FD5` | 3 | `1 ^ a ^ a & b & c` | 0xd5 |
| `FD6` | 3 | `a ^ b ^ c ^ b & c ^ a & b & c` | 0xd6 |
| `FD7` | 3 | `1 ^ a & b ^ a & c` | 0xd7 |
| `FD8` | 3 | `(a & b) | (!a & c)` | 0xd8 |
| `FD9` | 3 | `1 ^ a ^ b ^ b & c ^ a & b & c` | 0xd9 |
| `FDA` | 3 | `a ^ c ^ a & b & c` | 0xda |
| `FDB` | 3 | `1 ^ b ^ a & b ^ a & c ^ b & c` | 0xdb |
| `FDC` | 3 | `b ^ c ^ a & c ^ b & c ^ a & b & c` | 0xdc |
| `FDD` | 2 | `!a | b` | 0xdd |
| `FDE` | 3 | `a ^ b ^ a & b ^ c ^ b & c` | 0xde |
| `FDF` | 3 | `1 ^ a & c ^ a & b & c` | 0xdf |
| `FE0` | 3 | `a & c ^ b & c ^ a & b & c` | 0xe0 |
| `FE1` | 3 | `1 ^ a ^ b ^ a & b ^ c` | 0xe1 |
| `FE2` | 3 | `(a & c) | (b & !c)` | 0xe2 |
| `FE3` | 3 | `1 ^ b ^ c ^ a & c ^ a & b & c` | 0xe3 |
| `FE4` | 3 | `b ^ a & b ^ a & c` | 0xe4 |
| `FE5` | 3 | `1 ^ a ^ c ^ b & c ^ a & b & c` | 0xe5 |
| `FE6` | 3 | `a ^ b ^ a & b & c` | 0xe6 |
| `FE7` | 3 | `1 ^ a & b ^ c ^ a & c ^ b & c` | 0xe7 |
| `FE8` | 3 | `(a & b) | (a & c) | (b & c)` | 0xe8 |
| `FE9` | 3 | `1 ^ a ^ b ^ c ^ a & b & c` | 0xe9 |
| `FEA` | 3 | `a ^ b & c ^ a & b & c` | 0xea |
| `FEB` | 3 | `1 ^ b ^ a & b ^ c ^ a & c` | 0xeb |
| `FEC` | 3 | `b ^ a & c ^ a & b & c` | 0xec |
| `FED` | 3 | `1 ^ a ^ a & b ^ c ^ b & c` | 0xed |
| `FEE` | 2 | `a | b` | 0xee |
| `FEF` | 3 | `1 ^ c ^ a & c ^ b & c ^ a & b & c` | 0xef |
| `FF0` | 3 | `c` | 0xf0 |
| `FF1` | 3 | `1 ^ a ^ b ^ a & b ^ a & c ^ b & c ^ a & b & c` | 0xf1 |
| `FF2` | 3 | `a ^ a & b ^ c ^ a & c ^ a & b & c` | 0xf2 |
| `FF3` | 3 | `1 ^ b ^ b & c` | 0xf3 |
| `FF4` | 3 | `b ^ a & b ^ c ^ b & c ^ a & b & c` | 0xf4 |
| `FF5` | 3 | `1 ^ a ^ a & c` | 0xf5 |
| `FF6` | 3 | `a ^ b ^ c ^ a & c ^ b & c` | 0xf6 |
| `FF7` | 3 | `1 ^ a & b ^ a & b & c` | 0xf7 |
| `FF8` | 3 | `a & b ^ c ^ a & b & c` | 0xf8 |
| `FF9` | 3 | `1 ^ a ^ b ^ a & c ^ b & c` | 0xf9 |
| `FFA` | 3 | `a ^ c ^ a & c` | 0xfa |
| `FFB` | 3 | `1 ^ b ^ a & b ^ b & c ^ a & b & c` | 0xfb |
| `FFC` | 3 | `b ^ c ^ b & c` | 0xfc |
| `FFD` | 3 | `1 ^ a ^ a & b ^ a & c ^ a & b & c` | 0xfd |
| `FFE` | 3 | `a | b | c` | 0xfe |
| `FFF` | 0 | `1` | 0xff |
