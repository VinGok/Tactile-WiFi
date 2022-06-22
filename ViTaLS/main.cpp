// DQ-full-OFDMAsingle-lossless description
// DQ + video only in UL-OFDMA + AP schedules only one round of UL-OFDMA for each contention win --- video is transmitted with/without haptic piggybacking with multi-TID
// For now, better utilization of UL-OFDMA by also transmitting HA-only AMPDU by some STAs along with multi-TID AMPDUs from other STAs
// However, no visible improvement in performance than DQ-fullOFDMA-splitVideo

// Haptic and video streams being transmitted from each STA as AC_HA and AC_VI, respectively.
// Both streams generate frames at 1kHz
// OFDMA on DL and UL in batches of 4 or 2 or 1 with highest-first Tx.

// Full OFDMA and short retry count implemented for buffered scheme (BuS)
// RMSE measurement for DL by isolating latency experienced by one particular stream


// Commands for synchronizing with Github
// git add 80211ax-TI-OFDMA-Win
// git commit -m "comment"
// git push
// git status


#include <stdio.h>
#include <stdlib.h>     /* srand, rand */
#include <math.h>       /* ceil */
#include "ti_core.h"
#include <iostream>
#include <fstream>

using namespace std;

#define NUM_STATIONS 8
#define FRAGMENT_THRESHOLD 0.4

std::ofstream hap_file, vid_file, kin_file, global_buffer_file, frag_thresh;
void TIoperation(){
	struct wlan_result result;
	bool newSta;
	int buffer_limit_ap=1, buffer_limit_sta=1;
	srand (time(NULL));
	bool bw_mode = false;
	int ofdma_duration=50000;
	for (float fragment_threshold=0.34; fragment_threshold<=0.35; fragment_threshold=fragment_threshold+0.1){
		for (int buffer_limit=100; buffer_limit<=100; buffer_limit++){
			for (int nStas=1;nStas<=8;nStas++){
				newSta=true;
				for (int x=1; x<=1; x++){
					result = simulate_wlan(BANDWIDTH_80MHz, nStas, MCS_9, newSta, ofdma_duration, bw_mode, buffer_limit, fragment_threshold);
					newSta=false;
				}
			}
			hap_file << endl;
			vid_file << endl;
			kin_file << endl;
		}
	}
	hap_file << endl;
	vid_file << endl;
	kin_file << endl;
}


int main(int argc, char** argv) {
	printf("\n");
	freopen("./log/debug.txt","w",stdout);
	hap_file.open ("./log/hap_delay_p.txt", std::ofstream::out | std::ofstream::app);
	vid_file.open ("./log/vid_delay_p.txt", std::ofstream::out | std::ofstream::app);
	kin_file.open ("./log/kin_delay_p.txt", std::ofstream::out | std::ofstream::app);
	global_buffer_file.open ("ResultsFiles/Latency/Global/global_buffer.txt", std::ofstream::out);
	frag_thresh.open ("ResultsFiles/Latency/Global/frag_thresh.txt", std::ofstream::out);

	//	for (int i=1; i<=10; i++){
	TIoperation();
//	}

	printf("\n\nEnd of simulation\n");
	return 0;
}
