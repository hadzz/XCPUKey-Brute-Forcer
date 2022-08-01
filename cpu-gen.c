/*
 * Copyright Hect0r (c) 2016 - <sysop@staticpi.net>
 * XCPUKey-miner is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version.
 *
 * XCPUKey-miner is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with XCPUKey-miner.  If not, see <http://www.gnu.org/licenses/>
 */

/*
 * File:   cpu-gen.c
 * Author: Hect0r
 *
 * Created on 07 December 2016, 14:28
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <inttypes.h>
#include <math.h>
#include <unistd.h>
#include <sys/time.h>
#include <stdbool.h>
#include "crypto/enc/rc4.h"
#include "crypto/hash/hmac-sha1.h"

// Globals.
unsigned char * cpu_key, * serial_num;
uint8_t * kv_enc;
uint8_t * hmac;

int debug = 0, mine = 1;
int nthreads = 0;
uint64_t total_keys = 0;
unsigned int valid_keys = 0;
bool success = false;

pthread_mutex_t print_mutex;

typedef struct ModeOf {
  uint64_t Start;
  uint64_t Max;
  int ThreadNum;
} my_mode_t;


int verifyCPUKey(unsigned char * key) {
  int i, j;
  int hamming = 0;
  for (i = 0; i < 13; ++i) {
    for (j = 0; j < 8; ++j) {
      unsigned char mask = 1 << j;
      if ((key[i] & mask) != 0)
        hamming++;
    }
  }
  if ((key[13] & 1) == 1) hamming++;
  if ((key[13] & 2) == 2) hamming++;
  if (hamming != 53) return -1;
  return 0;
}

void keyECD(unsigned char * key, unsigned char * ecd) {
  int cnt;
  for (cnt = 0; cnt < 16; ++cnt)
    ecd[cnt] = key[cnt];

  unsigned int acc1 = 0, acc2 = 0;
  for (cnt = 0; cnt < 0x80; ++cnt, acc1 >>= 1) {
    unsigned char bTmp = ecd[cnt >> 3];
    unsigned int dwTmp = (unsigned int)((bTmp >> (cnt & 7)) & 1);
    if (cnt < 0x6A) {
      acc1 = dwTmp ^ acc1;
      if ((acc1 & 1) > 0)
        acc1 = acc1 ^ 0x360325;
      acc2 = dwTmp ^ acc2;
    } else if (cnt < 0x7F) {
      if (dwTmp != (acc1 & 1))
        ecd[(cnt >> 3)] = (unsigned char)((1 << (cnt & 7)) ^ (bTmp & 0xFF));
      acc2 = (acc1 & 1) ^ acc2;
    } else if (dwTmp != acc2)
      ecd[0xF] = (unsigned char)((0x80 ^ bTmp) & 0xFF);
  }
}

int previous_power_of_two( int x ) {
    if (x == 0) {
        return 0;
    }
    x |= (x >> 1);
    x |= (x >> 2);
    x |= (x >> 4);
    x |= (x >> 8);
    x |= (x >> 16);
    return x - (x >> 1);
}

/*
 * Brute Thread. old fashioned brute force the cpukey.
 */
void * brute_thread(void * buf) {
  my_mode_t * tm = buf;
  unsigned char key[16];
  unsigned char * kp = key;
  // right part of key itterated normally (22 bits actually used)
  // bits (2^22)-(2^17) & (2^15)-(2^0)
  unsigned int keyRight = 0;
  // left part of key (known hamming weight of 53) 
  // bits (2^127)-(2^23) & (2^17)-(2^16)
  char * keyLeft = (char * ) malloc(106 * sizeof(char));
  unsigned char * ecd = malloc(16);
  unsigned char * hmac_buf = malloc(16);
  unsigned char * hmac_key = malloc(16);

  // Init crypto support.
  struct rc4_state * rc4 = malloc(sizeof(struct rc4_state));
  // Outputs.
  uint8_t hmac_key_uint[20];
  uint8_t * kv_dec = malloc(172);

  int kn = 0, i, j;
  int print_ctr = 0;
  
  // Copy hmac.
  kn = 0;
  while (kn < 16) {
    hmac_buf[kn] = (unsigned char) hmac[kn];
    ++kn;
  }

  // Init keyLeft
  // each thread has its own "prefix bits" to divide up keys
  int prefix_bits = log2(nthreads);  // 8 threads = 3 prefix bits
  int bitsRemaining=53;
  j=prefix_bits-1;
  for (i = 0; i < prefix_bits; ++i) {
    if (((tm->ThreadNum >> j) & 1)) {
      keyLeft[i] = 1;
      bitsRemaining--;
    }
    else keyLeft[i] = 0;
    j--;
  }
  for (i = prefix_bits; i < prefix_bits + bitsRemaining; ++i)
    keyLeft[i] = 1;
  for (i = prefix_bits + bitsRemaining; i < 106; ++i)
    keyLeft[i] = 0;
  
  // set key's upper 13 bytes to 0
  for (i = 0; i < 13; ++i)
    kp[i] = 0;
  // copy / convert bit array into upper 13 bytes of key
  for (i = 0; i < 104; ++i) {
    kp[i / 8] |= ((keyLeft[i]) << (7 - (i % 8)));
  }
  
  pthread_mutex_lock(&print_mutex);
  printf("#%d Thread Started (Prefix: %02X"
    ", Mode: Gospers Hack)...\n",
    tm -> ThreadNum, tm -> ThreadNum);
  printf("Initial Key: ");
  kn = 0;
  while (kn < 16) {
    printf("%02X", kp[kn]);
    ++kn;
  }
  printf("\n");
  pthread_mutex_unlock(&print_mutex);

  bool done = false;
  while (!done && mine > 0) {
    // upper 6 bits of 14th byte come from keyRight
    kp[13] = (unsigned char)(((keyRight & 0xFF0000) >> 14));
    // 14th byte has 2 bits from keyLeft, mask 0x03
    if (keyLeft[104] == 1) kp[13] += 1;
    if (keyLeft[105] == 1) kp[13] += 2;
    kp[14] = (unsigned char)((keyRight & 0xFF00) >> 8);
    kp[15] = (unsigned char)(keyRight & 0xFF);
    
    while (mine > 0) {
      
      // check ECD to see if this key is valid
      keyECD(kp, ecd);
      if (memcmp(ecd, kp, 16) != 0) {
        if (keyRight == 0x3FFFFF) {
          keyRight = 0;
          break;
        }
        ++keyRight;
        kp[13] = (unsigned char)(((keyRight & 0xFF0000) >> 14) | (kp[13] & 0x3));
        kp[14] = (unsigned char)((keyRight & 0xFF00) >> 8);
        kp[15] = (unsigned char)(keyRight & 0xFF);
        total_keys++;
        continue;
      }
      
      ++print_ctr; 
      ++total_keys;
      ++valid_keys;
      if (print_ctr == 25) {
        pthread_mutex_lock(&print_mutex);
        printf("Thread %d Current Key: ", tm -> ThreadNum);
        kn = 0;
        while (kn < 16) {
          printf("%02X", kp[kn]);
          ++kn;
        }
        printf("\n");
        print_ctr = 0;
        pthread_mutex_unlock(&print_mutex);
      }
      
      // Generate Hmac Key for decryption.
      hmac_sha1(hmac_key, kp, 128, hmac_buf, 128);

      // Convert Hmac to uint8_t.
      kn = 0;
      while (kn < 16) {
        hmac_key_uint[kn] = (uint8_t) hmac_key[kn];
        ++kn;
      }
      
      // Decrypt kv_header and compare to known serial number.
      rc4_init(rc4, hmac_key_uint, 16);
      rc4_crypt(rc4, kv_enc, kv_dec, 172);
      //rc4_v(kv_enc, kv_dec, 172, hmac_key_uint, 16);
      
      // Compare The serial number.
      if (kv_dec[171] == (uint8_t) serial_num[11] &&
        kv_dec[170] == (uint8_t) serial_num[10] &&
        kv_dec[169] == (uint8_t) serial_num[9] &&
        kv_dec[168] == (uint8_t) serial_num[8] &&
        kv_dec[167] == (uint8_t) serial_num[7] &&
        kv_dec[166] == (uint8_t) serial_num[6] &&
        kv_dec[165] == (uint8_t) serial_num[5] &&
        kv_dec[164] == (uint8_t) serial_num[4] &&
        kv_dec[163] == (uint8_t) serial_num[3] &&
        kv_dec[162] == (uint8_t) serial_num[2] &&
        kv_dec[161] == (uint8_t) serial_num[1] &&
        kv_dec[160] == (uint8_t) serial_num[0]) {
        kn = 0;
        while (kn < 16) {
          cpu_key[kn] = kp[kn];
          ++kn;
        }
        mine = 0;
        done = true;
        success = true;
        break;
      } else { // Get a new cpu key for next round.
        // check it lower bits roll over
        if (keyRight == 0x3FFFFF) {
          keyRight = 0;
          // go to next keyLeft code
          break;
        }
        ++keyRight;
        kp[13] = (unsigned char)(((keyRight & 0xFF0000) >> 14) | (kp[13] & 0x3));
        kp[14] = (unsigned char)((keyRight & 0xFF00) >> 8);
        kp[15] = (unsigned char)(keyRight & 0xFF);
        
      }
    }
    if (done) break;
    // get the next valid bit permutation for keyLeft with weight 53
    for (i = prefix_bits; i < 105; ++i) {
      // from right to left: look for first one with a zero on its left
      if (keyLeft[i] == 1 && keyLeft[i + 1] == 0) {
        // swap
        keyLeft[i] = 0;
        keyLeft[i + 1] = 1;
        // shift all one bits from 0 to i to the far left
        int oneBits = 0;
        int zeroBits = 0;
        for (j = prefix_bits; j < i; ++j) {
          if (keyLeft[j] == 1) oneBits++;
          else zeroBits++;
        }
        for (j = prefix_bits; j < prefix_bits + oneBits; ++j)
          keyLeft[j] = 1;
        for (j = prefix_bits + oneBits; j < i; ++j)
          keyLeft[j] = 0;
        
        break;
      }
      // if no more one bits have a zero on its left, we are done
      else if (i == 104) {
        done = true;
        printf("Thread %d exiting...\n", tm->ThreadNum);
      }
    }
    // set key's upper 13 bytes to 0
    for (i = 0; i < 13; ++i)
      kp[i] = 0;
    // copy / convert bit array into upper 13 bytes of key
    for (i = 0; i < 104; ++i) {
      kp[i / 8] |= ((keyLeft[i]) << (7 - (i % 8)));
    }
  }
  free(keyLeft);
  free(ecd);
  free(hmac_buf);
  free(hmac_key);
  free(rc4);
  free(kv_dec);
  pthread_exit(NULL);
  return NULL;
}

/*
 * Count Processors, taken from vanitygen by samr7.
 */
#if!defined(_WIN32)
int count_processors(void) {
  FILE * fp;
  char buf[512];
  int count = 0;

  fp = fopen("/proc/cpuinfo", "r");
  if (!fp)
    return -1;

  while (fgets(buf, sizeof(buf), fp)) {
    if (!strncmp(buf, "processor\t", 10))
      count += 1;
  }
  fclose(fp);
  return count;
}
#endif
/*
 * Usage.
 */
void usage() {
  printf(
    "XCPUKey-Brute-Forcer - by Hect0r, fork by Hadzz\n"
    "Usage : cpu-gen [!keyvault_location] [!serial_number] [thread_count]\n"
    " NOTE : Each argument with a ! in it, needs to be set, without ! is "
    "optional.\n"
    "[keyvault_location] - The filepath to the ENCRYPTED keyvault.\n"
    "[serial_number] - Your console serial number, 12 numbers.\n"
    "[thread_count] - The number of cpu threads to use, default: num of cpu "
    "cores.\n");
}
/*
 * Main Entry point.
 */
/*
 unsigned char* uint64_to_uchar(uint64_t input) {
        unsigned char *buf = malloc(sizeof(input));
        memcpy(buf, &input, sizeof(input));
        return buf;
}
uint64_t uchar_to_uint64(unsigned char *input, int start, bool reverse)
*/
int main(int argc, char ** argv) {
  int t = 0, rc = 0;

  if (argc < 2) {
    usage();
    return EXIT_SUCCESS;
  }

  printf("XCPUKey-Brute-Forcer - by Hect0r, fork by Hadzz\n");

  FILE * kv = fopen(argv[1], "rb+");
  if (!kv) {
    printf("Unable to open kv file...\n");
    return 1;
  }
  fseek(kv, 0, SEEK_SET);
  hmac = malloc(16);
  if (fread(hmac, 16, 1, kv) != 1) {
    fprintf(stderr, "Cannot read HMAC from KeyVault file...\n");
    return 1;
  }
  if (debug == 1) {
    printf("HMAC Seed : ");

    t = 0;
    while (t < 16) {
      printf("%02X", hmac[t]);
      ++t;
    }
    printf("\n");
  }
  kv_enc = malloc(16368);
  fseek(kv, 16, SEEK_SET);
  if (fread(kv_enc, 16368, 1, kv) != 1) {
    fprintf(stderr, "Unable to read kv header from KeyVault...\n");
    return 1;
  }
  if (debug == 1) {
    printf("KV Header : ");
    t = 0;
    while (t < 16368) {
      printf("%02X", kv_enc[t]);
      ++t;
    }
    printf("\n");
  }

  if (argc >= 3) {
    t = 0;
    serial_num = malloc(12);
    if (debug == 1) {
      printf("Serial Number : ");
    }
    while (t < 12) {
      serial_num[t] = (unsigned char) argv[2][t];
      if (debug == 1) {
        printf("%02X", serial_num[t]);
      }
      ++t;
    }
    if (debug == 1) {
      printf("\n");
    }
  } else {
    fprintf(stderr, "Please provide your consoles serial number !");
    return 1;
  }
  
  cpu_key = malloc(16);

  if (argc == 3)
  {
    nthreads = 1;
#if!defined(_WIN32)
    nthreads = count_processors();
#endif
  }
  else if (argc >= 4) {
    nthreads = atoi(argv[3]);
#if!defined(_WIN32)
    if (nthreads < 1 || nthreads == 0 || nthreads > 16)
      nthreads = count_processors();
#endif
    
  }
  nthreads = previous_power_of_two(nthreads);
  printf("nthreads: %d\n", nthreads);

  if (debug == 1) {
    printf("KV Location %s\n"
      "Num Threads is %d\n",
      argv[1], nthreads);
  }

  pthread_t threads[nthreads];
  pthread_mutex_init(&print_mutex, NULL);

  // Start Mining Threads.
  for (t = 0; t < nthreads; ++t) {
    my_mode_t * buf = malloc(sizeof(*buf));
    buf -> ThreadNum = t;
    buf -> Start = ((53 / nthreads) * (t+1));
    buf -> Max = ((53 / nthreads) * (t));
    rc = pthread_create( & threads[t], NULL, brute_thread, (void * ) buf);
    if (rc) {
      fprintf(stderr, "ERROR: could not create thread %d\n", t);
      exit(1);
    }
  }

  struct timeval last_upd;
  struct timeval tv_now;

  gettimeofday( & tv_now, NULL);
  gettimeofday( & last_upd, NULL);

  int hashes = 0, start = 0;
  while (mine == 1) {
    start = total_keys;
    sleep(1);
    hashes = total_keys - start;
    if ((tv_now.tv_sec - last_upd.tv_sec) >= 5) {
      printf("[ KPS : %d k/ps - Total : %"
        PRIu64 " - Valid Keys : %d ]\n",
        hashes, total_keys, valid_keys);
      gettimeofday( & last_upd, NULL);
    }

    gettimeofday( & tv_now, NULL);
  }
  for (t = 0; t < nthreads; ++t) {
    pthread_join(threads[t], NULL);
  }
  // destroy mutex
  pthread_mutex_destroy(&print_mutex);
  
  if (success)
  {
    printf("\nKEY WAS FOUND! :)\n");
    printf("CPU Key : ");
    t = 0;
    while (t < 16) {
      printf("%02X", cpu_key[t]);
      ++t;
    }
    printf("\n");
  }
  else {
    printf("Failed to find CPU key! Program exiting...\n");
  }
  
  free(hmac);
  free(kv_enc);
  free(serial_num);
  free(cpu_key);
  return (EXIT_SUCCESS);
}