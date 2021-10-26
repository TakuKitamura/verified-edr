#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <net/if.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <errno.h>
#include <time.h>

#include <linux/can.h>
#include <linux/can/raw.h>

struct can_packet
{
    canid_t can_id; /* 32 bit CAN_ID + EFF/RTR/ERR flags */
    __u8 can_dlc;   /* data length code: 0 .. 8 */
    __u8 data[8] __attribute__((aligned(8)));
    time_t timestamp;
};

int getSocket()
{
    int s = socket(PF_CAN, SOCK_RAW, CAN_RAW);

    struct ifreq ifr;
    const char *ifname = "vcan0";
    strcpy(ifr.ifr_name, ifname);
    ioctl(s, SIOCGIFINDEX, &ifr);

    struct sockaddr_can addr;
    addr.can_family = AF_CAN;
    addr.can_ifindex = ifr.ifr_ifindex;

    // printf("%s at index %d\n", ifname, ifr.ifr_ifindex);

    if (bind(s, (struct sockaddr *)&addr, sizeof(addr)) == -1)
    {
        perror("Error in socket bind");
    }
    return s;
}

struct can_packet packetCapture(int fd)
{
    struct can_packet frame;
    // CANパケットキャプチャ
    while (1)
    {
        ssize_t n = read(fd, &frame, sizeof(struct can_packet));
        time(&frame.timestamp);
        if (n != -1)
        {
            return frame;
        }
        else
        {
            printf("error happens(errno=%d)\n", errno);
        }
    }
    // unreachable
    return frame;
}

void printFrame(struct can_packet frame)
{
    printf("can_id = 0x%x, can_dlc %d, can_data = [", frame.can_id, frame.can_dlc);
    for (int i = 0; i < 8; i++)
    {
        printf("0x%x", frame.data[i]);
        if (i == 7)
        {
            printf("]\n");
        }
        else
        {
            printf(", ");
        }
    }
}

int main(void)
{
    int fd = getSocket();
    while (1)
    {
        struct can_packet frame = packetCapture(fd);
        printFrame(frame);
    }
}
