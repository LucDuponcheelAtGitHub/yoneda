package notation

type Law[Z] = Tuple2[Z, Z]

def Law[Z]: Tuple2[Z, Z] => Law[Z] = identity
