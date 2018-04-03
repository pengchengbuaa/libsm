# Libsm

This is a Rust library of China's Standards of Encryption Algorithms.

SM3, SM4 and SM2 digital signature have already been implemented. But now the library is awfully slow: it takes 30ms to
verify a signature on my computer.

Some parts will be rewritten using SIMD.

