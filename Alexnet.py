from __future__ import absolute_import
from __future__ import division
from __future__ import print_function
import tensorflow as tf
import cv2
import sys
import numpy as np
import os
import glob
from random import shuffle


def multi_label_hot(prediction, threshold=0.5):
    prediction = tf.cast(prediction, tf.float32)
    threshold = float(threshold)
    return tf.cast(tf.greater(prediction, threshold), tf.int64)


def cnn_model_fn(features, labels, mode):

  # Sort labels
  if not (mode == tf.estimator.ModeKeys.PREDICT):
    num_labels = labels[:]

    # layers
    input_layer = tf.reshape(features["x"], [-1, 227, 227, 3])

    # Layer 1
    conv1 = tf.layers.conv2d(inputs=input_layer, name='layer_conv1',
                           filters=96, kernel_size=11, strides=4,
                           padding='valid', activation=tf.nn.relu)
    pool1 = tf.layers.max_pooling2d(inputs=conv1, pool_size=3, strides=2)
    norm1 = tf.nn.local_response_normalization(pool1, depth_radius=2,
                                             alpha=1e-4, beta=0.75, 
                                             bias=1.0, name='norm1')
    # Layer 2
    conv2 = tf.layers.conv2d(inputs=norm1, name='layer_conv2',
                           filters=256, kernel_size=5, strides=1,
                           padding='same', activation=tf.nn.relu)
    pool2 = tf.layers.max_pooling2d(inputs=conv2, pool_size=3, strides=2)
    norm2 = tf.nn.local_response_normalization(pool2, depth_radius=2,
                                             alpha=1e-4, beta=0.75,
                                             bias=1.0, name='norm2')
    # Layer 3
    conv3 = tf.layers.conv2d(inputs=norm2, name='layer_conv3',
                           filters=384, kernel_size=3, strides=1,
                           padding='same', activation=tf.nn.relu)
    
    # Layer 4
    conv4 = tf.layers.conv2d(inputs=conv3, name='layer_conv4',
                           filters=384, kernel_size=3, strides=1,
                           padding='same', activation=tf.nn.relu)

    # Layer 5
    conv5 = tf.layers.conv2d(inputs=conv4, name='layer_conv5',
                           filters=256, kernel_size=3, strides=1,
                           padding='same', activation=tf.nn.relu)
    pool5 = tf.layers.max_pooling2d(inputs=conv5, pool_size=3, strides=2)


    # Layer 6
    flat = tf.contrib.layers.flatten(pool5)
    dense6 = tf.layers.dense(inputs=flat, name='layer_fc6',    
                        units=4096, activation=tf.nn.relu)  
    
    dropout6 = tf.layers.dropout(dense6, rate=0.5, noise_shape=None, 
                        seed=None, training=(mode == tf.estimator.ModeKeys.TRAIN))

    # Layer 7
    dense7 = tf.layers.dense(inputs=dropout6, name='layer_fc7',    
                        units=4096, activation=tf.nn.relu)  
    
    dropout7 = tf.layers.dropout(dense7, rate=0.5, noise_shape=None, 
                        seed=None, training=(mode == tf.estimator.ModeKeys.TRAIN))
    
    # Layer 8
    dense8 = tf.layers.dense(inputs=dropout7, name='layer_fc_8',
                        units=6)
    logits = dense8
    
    # Generate predictions (for PREDICT and EVAL mode)
    blocknum_prediction = tf.sigmoid(logits)#, axis=1)
    one_hot_prediction = multi_label_hot(blocknum_prediction)
    predictions = {
      "probabilities": tf.sigmoid(logits, name="softmax_tensor"),
      "classes": one_hot_prediction
    }

  # Return predictions when in PREDICT mode
  if mode == tf.estimator.ModeKeys.PREDICT:
    return tf.estimator.EstimatorSpec(mode=mode, predictions=predictions)

  # Calculate Loss (for both TRAIN and EVAL modes)
  #loss = tf.losses.sparse_softmax_cross_entropy(labels=num_labels, logits=logits)
  loss = tf.nn.sigmoid_cross_entropy_with_logits(logits=logits, labels=num_labels)
  # loss has the same shape as logits: 1 loss per class and per sample in the batch
  loss = tf.reduce_mean(tf.reduce_sum(loss, axis=1))

  # Configure the Training Op (for TRAIN mode)
  if mode == tf.estimator.ModeKeys.TRAIN:
    #optimizer = tf.train.GradientDescentOptimizer(learning_rate=0.0005)
    optimizer = tf.train.AdamOptimizer(learning_rate=0.0005)
    train_op = optimizer.minimize(loss=loss, global_step=tf.train.get_global_step())
    return tf.estimator.EstimatorSpec(mode=mode, loss=loss, train_op=train_op)

  # Add evaluation metrics (for EVAL mode)
  eval_metric_ops = {"accuracy": tf.metrics.accuracy(labels=labels[:], predictions=predictions["classes"])}
  return tf.estimator.EstimatorSpec(mode=mode, loss=loss, eval_metric_ops=eval_metric_ops)

 
def parse_dataset(train_dataset_size):
    images = []
    labels = []
    images_resized = []

    # loading files from folder
    addrs = glob.glob('objs/*/*/*.png')
    shuffle(addrs)
    st = 0
    unst = 0
    for addr in addrs:
        images.append(cv2.imread(addr))
        label = []
        if 'stable' in addr: # 0 = stable, 1 = unstable
            st += 1
            label.append(0)
            if 'objs/stable/blue/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/stable/blue/'+addr[-18:]):
                  addrs.remove('objs/stable/blue/'+addr[-18:])
            else: label.append(0)
            if 'objs/stable/red/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/stable/red/'+addr[-18:]):
                  addrs.remove('objs/stable/red/'+addr[-18:])
            else: label.append(0)
            if 'objs/stable/green/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/stable/green/'+addr[-18:]):
                  addrs.remove('objs/stable/green/'+addr[-18:])
            else: label.append(0)
            if 'objs/stable/white/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/stable/white/'+addr[-18:]):
                  addrs.remove('objs/stable/white/'+addr[-18:])
            else: label.append(0)
            if 'objs/stable/yellow/'+addr[-18:] in addrs: 
                label.append(1)
                if not(addr == 'objs/stable/yellow/'+addr[-18:]):
                  addrs.remove('objs/stable/yellow/'+addr[-18:])
            else: label.append(0)

        else:
            unst += 1
            label.append(1)
            if 'objs/unstab/blue/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/unstab/blue/'+addr[-18:]):
                  addrs.remove('objs/unstab/blue/'+addr[-18:])
            else: label.append(0)
            if 'objs/unstab/red/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/unstab/red/'+addr[-18:]):
                  addrs.remove('objs/unstab/red/'+addr[-18:])
            else: label.append(0)
            if 'objs/unstab/green/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/unstab/green/'+addr[-18:]):
                  addrs.remove('objs/unstab/green/'+addr[-18:])
            else: label.append(0)
            if 'objs/unstab/white/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/unstab/white/'+addr[-18:]):
                  addrs.remove('objs/unstab/white/'+addr[-18:])
            else: label.append(0)
            if 'objs/unstab/yellow/'+addr[-18:] in addrs: 
                label.append(1)
                if not(addr == 'objs/unstab/yellow/'+addr[-18:]):
                  addrs.remove('objs/unstab/yellow/'+addr[-18:])
            else: label.append(0)         


        labels.append(label)

    # resize images to be 56x56
    for image in images:
        resized_image = cv2.resize(image, (227, 227))
        images_resized.append(resized_image) 

    # separate images and labels into train and test sets
    train_images = images_resized[0:train_dataset_size]
    training_labels = labels[0:train_dataset_size]
    test_images = images_resized[train_dataset_size:]
    test_labels = labels[train_dataset_size:]

    # convert dataset into numpy arrays
    train_data = np.asarray(train_images, np.float32)
    train_labels = np.asarray(training_labels, np.float32)
    eval_data = np.asarray(test_images, np.float32)
    eval_labels = np.asarray(test_labels, np.float32)

    return train_data, train_labels, eval_data, eval_labels


# MAIN
def train(train_dataset_size):

    tf.logging.set_verbosity(tf.logging.INFO)

    # get training and evaluation data
    train_data, train_labels, eval_data, eval_labels = parse_dataset(train_dataset_size)

    # Create the Estimator
    cnn = tf.estimator.Estimator(model_fn=cnn_model_fn, model_dir="models/alexnet")

    # Set up logging for predictions
    # Log the values in the "Softmax" tensor with label "probabilities"
    tensors_to_log = {"probabilities": "softmax_tensor"}
    logging_hook = tf.train.LoggingTensorHook(tensors=tensors_to_log, every_n_iter=50)

    # Train the model
    train_input_fn = tf.estimator.inputs.numpy_input_fn(
        x={"x": train_data},
        y=train_labels,
        batch_size=10,
        num_epochs=None,
        shuffle=True)
    cnn.train(
        input_fn=train_input_fn,
        steps=20000,
        hooks=[logging_hook])

    # Evaluate the model and print results
    eval_input_fn = tf.estimator.inputs.numpy_input_fn(
        x={"x": eval_data},
        y=eval_labels,
        num_epochs=1,
        shuffle=False)
    eval_results = cnn.evaluate(input_fn=eval_input_fn)
    print ('\nAccuracy:')
    print(eval_results)

    '''
    # Use CNN model to get predictions
    prediction_results = cnn.predict(input_fn=eval_input_fn)
    pred_list = list(prediction_results)
    for i in range(len(eval_data)):
        print ('Prediction:')
        print (pred_list[i])
        print ('Label:')
        print (eval_labels[i])
        print ('\n')
    '''

arg = list(sys.argv)
train_size = arg[-1]
train(int(train_size))
