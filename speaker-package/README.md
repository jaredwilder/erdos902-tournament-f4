# ERDOS902-SPEAKER-REAL-002

A real continuation on Erdős #902.

Replay:

```bash
python verify_real_002.py
```

The run:
- decodes all 37 raw DRT(23) representatives;
- independently re-identifies rows 35 and 36 as the only S3 cores;
- exhausts every admissible mask of every size 0..12;
- computes the exact repair-capacity profile;
- certifies the global word `ADMISSIBLE_REPAIR_CAPACITY = 66`;
- applies it to order 48 and the indegree-23 branch of order 49.

External boundary: completeness of the published 37-class DRT(23) catalogue.
