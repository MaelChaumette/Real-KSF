from lazylinop.butterfly import dct as lz_dct, dft as lz_fft
from lazylinop.butterfly import KsmPermLazyLinOp
from lazylinop.basicops import bitrev
from lazylinop.signal.dct import _reorder
from lazylinop import diag
from tqdm import tqdm
import time
import math
import torch
import warnings
import mlflow
import numpy as np

from array_api_compat import device

from os import environ

warnings.filterwarnings("ignore")


if "OMP_NUM_THREADS" in environ.keys():
    torch.set_num_threads(int(environ["OMP_NUM_THREADS"]))
else:
    torch.set_num_threads(4)


def fast_dct_complex(N, array_namespace, device):
    d = 2 * array_namespace.exp(-(1j * math.pi / (2 * N) * array_namespace.arange(
        0, N, dtype=array_namespace.float64, device=device)))
    d_ortho = array_namespace.ones(
        N, dtype=array_namespace.complex128, device=device) * 2 * math.sqrt(2 / N)
    d_ortho[0] = 2 * math.sqrt(1 / N)

    d_final = d * d_ortho
    D = diag(d_final)

    F = lz_fft(N, dtype=array_namespace.complex128, device=device)

    return (D @ F @ bitrev(N) @ _reorder(N)).real


def fast_dct_real(N, device, array_namespace, target_dtype=None):
    if target_dtype is None:
        target_dtype = array_namespace.float64

    _, B_lz, R_lz = lz_dct(
        N, 2, dtype=array_namespace.float64, device=device, output="LBPR")

    # Quantization step
    ksv_B = B_lz.ks_values
    ksv_B = [
        np.asarray(ksv_B[i], dtype=target_dtype, device=device)
        for i in range(len(ksv_B))
    ]
    B_lz = KsmPermLazyLinOp(ksv_B)
    return B_lz @ R_lz


def time_matrix_vector_product(L, x, n_trials=100, n_events=100):
    warnings.filterwarnings("ignore")

    n, b = x.shape

    _device = device(x)
    start = torch.Event(enable_timing=True)
    end = torch.Event(enable_timing=True)
    # Warmup
    for _ in range(n_events):
        L @ x

    all_times = [None] * n_trials
    for i in tqdm(range(n_trials), desc=f"n={n}, b={b}, device={_device}"):
        if _device == "cuda":
            start.record()
        else:
            start = time.time()

        for _ in range(n_events):
            L @ x

        if _device == "cuda":
            end.record()
            end.synchronize()

            all_times[i] = 1e-3 * start.elapsed_time(end) / n_events
        else:
            all_times[i] = (time.time() - start) / n_events

    return all_times


def computational_costs(n, b, device, n_trials=100, n_events=100):
    mlflow.set_experiment("Computational costs DCT methods")

    if device == "cuda":
        xp = torch
    else:
        xp = np

    dct_complex128 = fast_dct_complex(n, array_namespace=xp, device=device)
    dct_float64 = fast_dct_real(
        n, device, array_namespace=xp, target_dtype=xp.float64)

    if device == "cuda":
        dct_float16 = fast_dct_real(
            n, device, array_namespace=torch, target_dtype=torch.float16)
        dct_bfloat16 = fast_dct_real(
            n, device, array_namespace=torch, target_dtype=torch.bfloat16)

    with mlflow.start_run(run_name=f"n={n} - b={b} - device={device}"):
        mlflow.log_param("n", n)
        mlflow.log_param("b", b)
        mlflow.log_param("device", device)

        mlflow.set_tag("version", "v2")

        if device == "cuda":
            x = torch.randn(n, b, dtype=torch.float64, device=device)

            time_complex128 = time_matrix_vector_product(dct_complex128, x.to(
                torch.complex128), n_trials=n_trials, n_events=n_events)
            time_float64 = time_matrix_vector_product(
                dct_float64, x, n_trials=n_trials, n_events=n_events)
            time_float16 = time_matrix_vector_product(dct_float16, x.to(
                torch.float16), n_trials=n_trials, n_events=n_events)
            time_bfloat16 = time_matrix_vector_product(dct_bfloat16, x.to(
                torch.bfloat16), n_trials=n_trials, n_events=n_events)
        else:
            x = np.random.randn(n, b).astype(np.float64)

            time_complex128 = time_matrix_vector_product(dct_complex128, x.astype(
                np.complex128), n_trials=n_trials, n_events=n_events)
            time_float64 = time_matrix_vector_product(
                dct_float64, x, n_trials=n_trials, n_events=n_events)
            time_float16 = np.nan
            time_bfloat16 = np.nan

        mlflow.log_metric("time_complex128", np.mean(time_complex128))
        mlflow.log_metric("time_float64", np.mean(time_float64))
        mlflow.log_metric("time_float16", np.mean(time_float16))
        mlflow.log_metric("time_bfloat16", np.mean(time_bfloat16))


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        description="Computational costs of DCT methods")
    parser.add_argument("--n", type=int, required=True,
                        help="Size of the input vector")
    parser.add_argument("--b", type=int, default=1, help="Batch size")
    parser.add_argument("--device", type=str, default="cpu",
                        help="Device to use (cpu or cuda)")
    parser.add_argument("--n_trials", type=int, default=100,
                        help="Number of trials for timing")
    parser.add_argument("--n_events", type=int, default=100,
                        help="Number of events for timing")

    args = parser.parse_args()

    computational_costs(args.n, args.b, args.device,
                        n_trials=args.n_trials, n_events=args.n_events)
