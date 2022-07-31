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
#include <unistd.h>
#include <sys/time.h>
#include <stdbool.h>
#include "crypto/enc/rc4.h"
#include "crypto/hash/hmac-sha1.h"

// Globals.
unsigned char *cpu_key, *serial_num;
uint8_t *kvheader;
uint8_t *hmac;

int debug = 0, mine = 1;
uint64_t total_keys = 0;
uint64_t valid_keys = 0;

typedef struct ModeOf {
  uint64_t Start;
  uint64_t Max;
  int ThreadNum;
} mode_t;

int verifyCPUKey (unsigned char* key) {
  int i, j;
  int hamming = 0;
  for (i=0; i<13; i++) {
    for (j=0; j<8; j++) {
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

void keyECD (unsigned char* key, unsigned char* ecd) {
  int cnt;
  for (cnt=0; cnt<16; cnt++)
    ecd[cnt] = key[cnt];
  
  unsigned int acc1 = 0, acc2 = 0;
  for (cnt=0; cnt< 0x80; cnt++, acc1 >>= 1) {
    unsigned char bTmp = ecd[cnt >> 3];
    unsigned int dwTmp = (unsigned int) ((bTmp >> (cnt & 7)) & 1);
    if (cnt < 0x6A) {
      acc1 = dwTmp ^ acc1;
      if ((acc1 & 1) > 0)
        acc1 = acc1 ^ 0x360325;
      acc2 = dwTmp ^ acc2;
    }
    else if (cnt < 0x7F) {
      if (dwTmp != (acc1 & 1))
        ecd[(cnt >> 3)] = (unsigned char)((1 << (cnt & 7)) ^ (bTmp & 0xFF));
      acc2 = (acc1 & 1) ^ acc2;
    }
    else if (dwTmp != acc2)
      ecd[0xF] = (unsigned char)((0x80 ^ bTmp) & 0xFF);
  }
}



/*
 * Brute Thread. old fashioned brute force the cpukey.
 */
void *brute_thread(void *buf) {
  mode_t *tm = buf;
  printf("#%d Thread Started (Starting Index: %" PRIu64 ", Max Index: %" PRIu64
         ", Mode: Increment)...\n",
         tm->ThreadNum, tm->Start, tm->Max);
  
  // testing key: DF AC 65 E8 B2 52 4E B8 4A 6B 7D 20 70 35 06 0C
  // serial: 057469473207
  //unsigned char key[16] = { 0xDF, 0xAC, 0x65, 0xE8, 0xB2,
   //0x52, 0x4E, 0xB8, 0x4A, 0x6B, 0x7D, 0x20, 0x70, 0x35,
   //0x06, 0x0C }, * kp = key;
  // full cpu key used to decrypt kv
  unsigned char key[16], *kp = key;
  // lower part of key itterated with each hamming code
  unsigned int keyLSB = 0;
  unsigned char *hmac_buf;
  unsigned char *hmac_key = malloc(16);
  unsigned char *ecd = malloc(16);
  char *hamming = (char*)malloc(106 * sizeof(char));
  int i,j;
  
  // Init crypto support.
  rc4_state_t *rc4 = malloc(sizeof(rc4_state_t));
  // Outputs.
  uint8_t buf2[20];
  uint8_t *buf4 = malloc(172);

  int kn = 0;

  // Copy hmac.
  hmac_buf = malloc(16);
  kn = 0;
  while (kn < 16) {
    hmac_buf[kn] = (unsigned char)hmac[kn];
    kn++;
  }
  
  // Init hamming code
  for (i=0; i<53; i++)
    hamming[i] = 0;
  for (i=53; i<106; i++)
    hamming[i] = 1;
  
  bool done = false;
  while (!done) {
    done = true;
    
    for (i=0; i<13; i++)
      kp[i] = 0;
    for (i=0; i<104; i++)
      kp[i/8] |= ((hamming[i])<< (7-(i%8)));
    kp[13] = (unsigned char)(((keyLSB & 0xFF0000) >> 14)) ;
    if (hamming[104] == 1) kp[13] += 1;
    if (hamming[105] == 1) kp[13] += 2;
    kp[14] = (unsigned char)((keyLSB & 0xFF00) >> 8);
    kp[15] = (unsigned char)(keyLSB & 0xFF);
    
    while (mine > 0) {  
      keyECD(kp, ecd);
      if (memcmp(ecd, kp, 16) != 0) {
        if (keyLSB == 0x3FFFFF) {
            keyLSB=0;
            break;
          }
          keyLSB++;
          kp[13] = (unsigned char)(((keyLSB & 0xFF0000) >> 14) | (kp[13] & 0x3));
          kp[14] = (unsigned char)((keyLSB & 0xFF00) >> 8);
          kp[15] = (unsigned char)(keyLSB & 0xFF);
          total_keys++;
          continue;
      }
      
      if (valid_keys % 20 == 0){
        printf("Thread %d Current Key: ", tm->ThreadNum);
        kn = 0;
        while (kn < 16) {
          printf("%02X", kp[kn]);
          kn++;
        }
        printf("\n");
      }

      // Generate Hmac Key for decryption.
      hmac_sha1(hmac_key, kp, 128, hmac_buf, 128);

      // Convert Hmac to uint8_t.
      kn = 0;
      while (kn < 16) {
        buf2[kn] = (uint8_t)hmac_key[kn];
        kn++;
      }

      // Decrypt kv_header and compare to know serial number.
      rc4_init(rc4, buf2, 16);
      rc4_crypt(rc4, kvheader, &buf4, 172);
            
      // Compare The serial number.
      if (buf4[171] == (uint8_t)serial_num[11] &&
        buf4[170] == (uint8_t)serial_num[10] &&
        buf4[169] == (uint8_t)serial_num[9] &&
        buf4[168] == (uint8_t)serial_num[8] &&
        buf4[167] == (uint8_t)serial_num[7] &&
        buf4[166] == (uint8_t)serial_num[6] &&
        buf4[165] == (uint8_t)serial_num[5] &&
        buf4[164] == (uint8_t)serial_num[4] &&
        buf4[163] == (uint8_t)serial_num[3] &&
        buf4[162] == (uint8_t)serial_num[2] &&
        buf4[161] == (uint8_t)serial_num[1] &&
        buf4[160] == (uint8_t)serial_num[0]) {
        printf("Found Key : ");
        kn = 0;
        while (kn < 16) {
          printf("%02X", kp[kn]);
          kn++;
        }
        printf("\n");
        mine = 0;
        done = true;
        pthread_exit(NULL);
      } 
      else { // Get a new cpu key for next round.
        // check it lower bits roll over
        if (keyLSB == 0x3FFFFF) {
          keyLSB=0;
          // go to next hamming code
          break;          
        }
        keyLSB++;
        kp[13] = (unsigned char)(((keyLSB & 0xFF0000) >> 14) | (kp[13] & 0x3));
        kp[14] = (unsigned char)((keyLSB & 0xFF00) >> 8);
        kp[15] = (unsigned char)(keyLSB & 0xFF);
        valid_keys++;
      }
    }
    // get the next valid hamming code
    for (i=105; i>0; i--) {
      // from right to left: look for first one with 
      // a zero on its left
      if (hamming[i] == 1 && hamming[i-1] == 0) {
        done = false;
        // swap
        hamming[i] = 0;
        hamming[i-1] = 1;
        // shift all one bits from i to length all 
        // the way to the right
        int oneBits = 0;
        int zeroBits = 0;
        for (j=i+1; j<106; j++) {
          if (hamming[j] == 1) oneBits++;
          else zeroBits++;
        }
        for (j=i+1; j<i+1+zeroBits; j++)
          hamming[j] = 0;
        for (j=i+1+zeroBits; j<106; j++)
          hamming[j] = 1;
        break;
      }
    }
  }

  pthread_exit(NULL);
}

/*
 * Count Processors, taken from vanitygen by samr7.
 */
#if !defined(_WIN32)
int count_processors(void) {
  FILE *fp;
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
int main(int argc, char **argv) {
  int nthreads = 0, t = 0, rc = 0;

  if (argc < 2) {
    usage();
    return EXIT_SUCCESS;
  }

  printf("XCPUKey-Brute-Forcer - by Hect0r, fork by Hadzz\n");

  FILE *kv = fopen(argv[1], "r");
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
      t++;
    }
    printf("\n");
  }
  kvheader = malloc(16368);
  fseek(kv, 16, SEEK_SET);
  if (fread(kvheader, 16368, 1, kv) != 1) {
    fprintf(stderr, "Unable to read kv header from KeyVault...\n");
    return 1;
  }
  if (debug == 1) {
    printf("KV Header : ");
    t = 0;
    while (t < 16368) {
      printf("%02X", kvheader[t]);
      t++;
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
      serial_num[t] = (unsigned char)argv[2][t];
      if (debug == 1) {
        printf("%02X", serial_num[t]);
      }
      t++;
    }
    if (debug == 1) {
      printf("\n");
    }
  } else {
    fprintf(stderr, "Please provide your consoles serial number !");
    return 1;
  }
  
  /*
  if (argc >= 4) {
    nthreads = atoi(argv[3]);

    if (nthreads < 0 || nthreads == 0 || nthreads > 16) {
      nthreads = count_processors();
    }
  }*/
  
  // threads limited to 1 until new code is finished
  nthreads = 1;
  
  if (debug == 1) {
    printf("KV Location %s\n"
           "Num Threads is %d\n",
           argv[1], nthreads);
  }

  pthread_t threads[nthreads];

  // Start Mining Threads.
  for (t = 0; t < nthreads; t++) {
    mode_t *buf = malloc(sizeof(mode_t));
    buf->ThreadNum = t;
    buf->Start = ((UINT64_MAX / nthreads) * t);
    buf->Max = buf->Start + (UINT64_MAX / nthreads);
    rc = pthread_create(&threads[t], NULL, brute_thread, (void *)buf);
    if (rc) {
      fprintf(stderr, "ERROR: could not create thread %d\n", t);
      exit(1);
    }
  }

  struct timeval last_upd;
  struct timeval tv_now;

  gettimeofday(&tv_now, NULL);
  gettimeofday(&last_upd, NULL);

  int hashes = 0, start = 0;
  while (mine == 1) {
    start = total_keys;
    sleep(1);
    hashes = total_keys - start;
    if ((tv_now.tv_sec - last_upd.tv_sec) >= 5) {
      printf("[ KPS : %d k/ps - Total : %" PRIu64 " - Valid Keys : %" PRIu64 " ]\n", hashes, total_keys, valid_keys);
      gettimeofday(&last_upd, NULL);
    }

    gettimeofday(&tv_now, NULL);
  }
  pthread_exit(NULL);
  return (EXIT_SUCCESS);
}