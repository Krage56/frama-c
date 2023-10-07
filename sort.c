// 1
void cocktail_fwd(int *arr, int n) {
    int swapped = 1;
    int start = 0;
    int end = n - 1;

    while (swapped > 0) {
        int i, tmp;

        swapped = 0;
        for (i = start; i < end; ++i) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
            }
        }

        if (!swapped)
            break;
        --end;

        swapped = 0;
        for (i = end - 1; i >= start; --i) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
            }
        }
        ++start;
    }
}

// 2
void cocktail_back(int *arr, int n) {
    int swapped = 1;
    int start = 0;
    int end = n - 1;

    while (swapped > 0) {
        int i, tmp;

        swapped = 0;
        for (i = end - 1; i >= start; --i) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
            }
        }

        if (!swapped)
            break;
        ++start;

        swapped = 0;
        for (i = start; i < end; ++i) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
            }
        }
        --end;
    }
}

// 3
#define UPPER_LIMIT 255

void count_pos(int *arr, int n) {
    int count[UPPER_LIMIT + 1];
    int i, j;

    for (i = 0; i <= UPPER_LIMIT; ++i) {
        count[i] = 0;
    }

    for (i = 0; i < n; ++i) {
        ++count[arr[i]];
    }

    for (i = 1; i <= UPPER_LIMIT; ++i) {
        count[i] += count[i - 1];
    }
    
    for (i = 0; i < UPPER_LIMIT; ++i) {
        for (j = count[i]; j < count[i + 1]; ++j) {
            arr[j] = i;
        }
    }
    for (j = count[UPPER_LIMIT]; j < n; ++j) {
        arr[j] = UPPER_LIMIT;
    }
}

// 4
#define UPPER_LIMIT 255

void count_num(int *arr, int n) {
    int count[UPPER_LIMIT + 1];
    int i, j, pos;

    for (i = 0; i <= UPPER_LIMIT; ++i) {
        count[i] = 0;
    }

    for (i = 0; i < n; ++i) {
        ++count[arr[i]];
    }

    pos = 0;
    for (i = 0; i <= UPPER_LIMIT; ++i) {
        for (j = 0; j < count[i]; ++j) {
            arr[j] = i;
        }
        pos += count[i];
    }
}

// 5
void bubble_lr(int *arr, int n) {
    int i, j, tmp;
    for (i = 0; i < n - 1; i++) {
        for (j = 0; j < n - i - 1; j++) {
            if (arr[j] > arr[j + 1]) {
                tmp = arr[j];
                arr[j] = arr[j + 1];
                arr[j + 1] = tmp;
            }
        }
    }
}

// 6
void bubble_rl(int *arr, int n) {
    int i, j, tmp;
    for (i = 0; i < n - 1; ++i) {
        for (j = n - 1; j > i; --j) {
            if (arr[j] < arr[j - 1]) {
                tmp = arr[j];
                arr[j] = arr[j - 1];
                arr[j - 1] = tmp;
            }
        }
    }
}

// 7
void insertion_lr(int *arr, int n) {
    int i, key, j;
    for (i = 1; i < n; i++) {
        key = arr[i];
        for (j = i - 1; j >= 0 && arr[j] > key; --j) {
            arr[j + 1] = arr[j];
        }
        arr[j + 1] = key;
    }
}

// 8
void insertion_rl(int *arr, int n) {
    int i, key, j;
    for (i = n - 2; i >= 0; --i) {
        key = arr[i];
        for (j = i + 1; j < n && arr[j] < key; ++j) {
            arr[j - 1] = arr[j];
        }
        arr[j - 1] = key;
    }
}

// 9
void shell_lr(int *arr, int n) {
    int i, j, tmp, gap;
    for (gap = n / 2; gap > 0; gap /= 2) {
        for (i = gap; i < n; ++i) {
            tmp = arr[i];
            for (j = i; j >= gap && arr[j - gap] > tmp; j -= gap) {
                arr[j] = arr[j - gap];
            }
            arr[j] = tmp;
        }
    }
}

// 10
void shell_rl(int *arr, int n) {
    int i, j, tmp, gap;
    for (gap = n / 2; gap > 0; gap /= 2) {
        for (i = n - gap; i >= 0; --i) {
            tmp = arr[i];
            for (j = i; j < n - gap && arr[j + gap] < tmp; j += gap) {
                arr[j] = arr[j + gap];
            }
            arr[j] = tmp;
        }
    }
}

// 11
void gnome_lr(int *arr, int n) {
    int tmp, idx = 0;

    while (idx < n) {
        if (idx == 0) {
            idx++;
        }
        if (arr[idx] >= arr[idx - 1]) {
            idx++;
        } else {
            tmp = arr[idx];
            arr[idx] = arr[idx - 1];
            arr[idx - 1] = tmp;
            idx--;
        }
    }
    return;
}

// 12
void gnome_rl(int *arr, int n) {
    int tmp, idx = n - 1;

    while (idx >= 0) {
        if (idx == n - 1) {
            idx--;
        }
        if (arr[idx] <= arr[idx + 1]) {
            idx--;
        } else {
            tmp = arr[idx];
            arr[idx] = arr[idx + 1];
            arr[idx + 1] = tmp;
            idx++;
        }
    }
}

// 13
void oddeven_lr(int *arr, int n) {
    int i, tmp, cnt = 1;
    while (cnt > 0) {
        cnt = 0;
        for (i = 1; i <= n - 2; i = i + 2) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++cnt;
            }
        }
        for (i = 0; i <= n - 2; i = i + 2) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++cnt;
            }
        }
    }
}

// 14
void oddeven_rl(int *arr, int n) {
    int i, tmp, cnt = 1;
    while (cnt > 0) {
        cnt = 0;
        for (i = n - 1; i > 0; i -= 2) {
            if (arr[i] < arr[i - 1]) {
                tmp = arr[i];
                arr[i] = arr[i - 1];
                arr[i - 1] = tmp;
                ++cnt;
            }
        }
        for (i = n - 2; i > 0; i -= 2) {
            if (arr[i] < arr[i - 1]) {
                tmp = arr[i];
                arr[i] = arr[i - 1];
                arr[i - 1] = tmp;
                ++cnt;
            }
        }
    }
}

// 15
void cycle_lr(int *arr, int n) {
    int lo, idx, x, i, tmp;
    for (lo = 0; lo <= n - 2; lo++) {
        x = arr[lo];
        idx = lo;

        for (i = lo + 1; i < n; i++) {
            if (arr[i] < x) {
                idx++;
            }
        }

        if (idx == lo) {
            continue;
        }

        while (x == arr[idx]) {
            idx += 1;
        }

        if (idx != lo) {
            tmp = arr[idx];
            arr[idx] = x;
            x = tmp;
        }

        while (idx != lo) {
            idx = lo;

            for (i = lo + 1; i < n; i++) {
                if (arr[i] < x) {
                    idx += 1;
                }
            }

            while (x == arr[idx]) {
                idx += 1;
            }

            if (x != arr[idx]) {
                tmp = arr[idx];
                arr[idx] = x;
                x = tmp;
            }
        }
    }
}

// 16
void cycle_rl(int *arr, int n) {
    int lo, idx, x, i, tmp;
    for (lo = n - 1; lo > 0; --lo) {
        x = arr[lo];
        idx = lo;

        for (i = lo - 1; i >= 0; --i) {
            if (arr[i] > x) {
                --idx;
            }
        }

        if (idx == lo) {
            continue;
        }

        while (x == arr[idx]) {
            --idx;
        }

        if (idx != lo) {
            tmp = arr[idx];
            arr[idx] = x;
            x = tmp;
        }

        while (idx != lo) {
            idx = lo;

            for (i = lo - 1; i >= 0; --i) {
                if (arr[i] > x) {
                    --idx;
                }
            }

            while (x == arr[idx]) {
                --idx;
            }

            if (x != arr[idx]) {
                tmp = arr[idx];
                arr[idx] = x;
                x = tmp;
            }
        }
    }
}
